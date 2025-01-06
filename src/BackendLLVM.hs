{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE LambdaCase #-}
module BackendLLVM ( emitLLVM ) where

import Latte.Abs
import Control.Monad.Except ( throwError, runExceptT, ExceptT, runExcept )

import Control.Monad.RWS (RWST (runRWST), tell)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader (local), ask)
import Control.Monad.Identity (Identity (runIdentity))
import Data.Map (Map, empty, fromList, lookup, union, size, insert)
import qualified Data.Map
import Data.Sequence (singleton, Seq, intersperse)
import Control.Monad.State (State, StateT (runStateT), runState, gets, modify)
import Control.Monad.Writer (WriterT (runWriterT))
import qualified Data.Foldable
import qualified Control.Monad.RWS as Data.Sequence
import qualified Data.List
import Data.Maybe (Maybe)
import Data.Foldable (toList)
import Debug.Trace (trace, traceShow)
import GHC.IO (unsafePerformIO)
import System.Posix.Internals (st_mtime)

data Value = Register Integer | RegisterPtr Integer | I32 Integer | I1 Bool | I8Ptr Integer Integer deriving (Eq)
instance Show Value where
    show (Register i) = "%v" ++ show i
    show (RegisterPtr i) = "%v" ++ show i
    show (I32 i) = show i
    show (I1 True) = "true"
    show (I1 False) = "false"
    show (I8Ptr ind length) = "getelementptr inbounds([" ++ show length ++ " x i8], [" ++ show length ++ "x i8]* @strings" ++ show ind ++ ", i32 0, i32 0)"

data St = St {
    strings :: Map String Integer,
    currentLoc :: Integer,
    currentResult :: Value,
    currentLabel :: Integer,
    localVars :: Map Ident Value
}
initState :: St
initState = St {
    strings = Data.Map.empty,
    currentLoc = 0,
    currentResult = Register 0,
    currentLabel = 0,
    localVars = Data.Map.empty
}

addNewString :: String -> IM Integer
addNewString str = do
    strings <- gets strings
    case Data.Map.lookup str strings of
        Just ind -> return ind
        Nothing -> do
            let ind = toInteger $ Data.Map.size strings
            modify (\st -> st { strings = Data.Map.insert str ind strings })
            return ind

data Env = Env {
    var :: Map Ident Value,
    returnType :: Maybe String,
    functionRetTypes :: Map String (Type' BNFC'Position),
    functionArgTypes :: Map String [Type' BNFC'Position]
}
initEnv :: Env
initEnv = Env {
    var = Data.Map.empty,
    returnType = Nothing,
    functionRetTypes = Data.Map.fromList [
        ("printInt", TVoid BNFC'NoPosition),
        ("printString", TVoid BNFC'NoPosition),
        ("error", TVoid BNFC'NoPosition),
        ("readInt", TInt BNFC'NoPosition),
        ("readString", TStr BNFC'NoPosition)
        ],
    functionArgTypes = Data.Map.fromList [
        ("printInt", [TInt BNFC'NoPosition]),
        ("printString", [TStr BNFC'NoPosition]),
        ("error", []),
        ("readInt", []),
        ("readString", [])
        ]
}
-- type IM = WriterT (Data.Sequence.Seq String) (State St)
-- runIM :: IM a -> St -> (a, St, Data.Sequence.Seq String)
-- runIM k s = 
--     let ((result, output), newstate) = runState (runWriterT k) s
--     in (result, newstate, output)
type IM = ReaderT Env (State St)
runIM :: IM a -> Env -> St -> (a, St)
runIM k env = runState (runReaderT k env)

class Compilable a where
    compile :: a -> IM (Data.Sequence.Seq String)

filterFuns :: [TopDefC] -> [FunDefC]
filterFuns = foldr f [] where
    f :: TopDefC -> [FunDefC] -> [FunDefC]
    f (FunDefTop _ fundef) acc = fundef : acc
    f _ acc = acc

emitLLVM :: ProgramC -> String
emitLLVM prog@(Program _ topDefs) = do
    let funs = filterFuns topDefs
    let functionRetTypes' = fromList $ map (\(FunDef _ retType (Ident name) _ _) -> (name, retType)) funs
    let initFunRetTypes = functionRetTypes initEnv
    let functionRetTypes = Data.Map.union functionRetTypes' initFunRetTypes
    let functionArgTypes' = fromList $ map (\(FunDef _ _ (Ident name) args _) -> (name, map (\(Arg _ type_ _) -> type_) args)) funs
    let initFunArgTypes = functionArgTypes initEnv
    let functionArgTypes = Data.Map.union functionArgTypes' initFunArgTypes
    let (output, _) = runIM (compile prog) (initEnv {functionRetTypes = functionRetTypes, functionArgTypes = functionArgTypes}) initState
    concat $ Data.Foldable.toList output

instance Compilable ProgramC where
    compile (Program _ topDefs) = do
        let initCode = Data.Sequence.singleton $ unlines [
                "declare void @printInt(i32)",
                "declare void @printString(i8*)",
                "declare void @error()",
                "declare i32 @readInt()",
                "declare i8* @readString()"
                ]
        compiledTopDefs <- traverse compile topDefs
        let code = mconcat compiledTopDefs
        allStrings <- gets strings
        let llvmStrings = unlines $ map (\(str, ind) -> "@strings" ++ show ind ++ " = private unnamed_addr constant [" ++ show (length str + 1) ++ " x i8] c\"" ++ str ++ "\\00\"") $ Data.Map.toList allStrings
        return $ initCode <> singleton llvmStrings <> code

instance Compilable TopDefC where
    compile (FunDefTop _ def) = compile def
    compile (ClsDefTop _ def) = error "Classes not supported"

instance Compilable (Type' BNFC'Position) where
    compile (TInt _) = pure $ Data.Sequence.singleton "i32"
    compile (TStr _) = pure $ Data.Sequence.singleton "i8*"
    compile (TBool _) = pure $ Data.Sequence.singleton "i1"
    compile (TVoid _) = pure $ Data.Sequence.singleton "void"

instance Compilable (ArgC' BNFC'Position) where
    compile (Arg _ typ (Ident name)) = do
        llvmType <- concat . toList <$> compile typ
        return $ singleton $ llvmType ++ " %" ++ name

instance Compilable FunDefC where
    compile (FunDef _ retType (Ident name) args block) = do
        llvmType <- concat . toList <$> compile retType
        argsCompiled <- toList . mconcat <$> traverse compile args
        let argsStr = Data.List.intercalate ", " argsCompiled
        let header = Data.Sequence.singleton $ unlines [
                "define " ++ llvmType ++ " @" ++ name ++ "(" ++ argsStr ++ ") {"
                ]
        initLoc <- gets currentLoc
        varLocs <- traverse (\(Arg _ _ (Ident name)) -> do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                return (Ident name, RegisterPtr loc)
                ) args
        modify (\st -> st { currentLoc = initLoc })
        loadArgs <- mconcat . map singleton <$> traverse (\(Arg _ type_ (Ident name)) -> do
                llvmType <- concat . toList <$> compile type_
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                return $ "%v" ++ show loc ++ " = alloca " ++ llvmType ++ "\n" ++
                    "store " ++ llvmType ++ " %" ++ name ++ ", " ++ llvmType ++ "* %v" ++ show loc ++ " ; already loaded\n"
                ) args
        let newVars = Data.Map.fromList varLocs
        body <- local (\env -> env { returnType = Just llvmType, var = newVars }) $ do
            compile block
        return $ header <> loadArgs <> body <> Data.Sequence.singleton "\n}\n"

instance Compilable BlockC where
    compile (Block _ []) = pure $ singleton "ret void\n"
    compile (Block _ stmts) = do        
        prev_vars <- gets localVars
        -- if block ends with cond or cond else, add dummy ret after it
        env <- ask
        let retStmt = case returnType env of
                Just "void" -> SRetVoid BNFC'NoPosition
                Just _ -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                Nothing -> error "Internal compiler error: return type not set"
        let stmts' = case last stmts of
                SCond _ _ _ -> stmts ++ [retStmt]
                SCondElse _ _ _ _ -> stmts ++ [retStmt]
                _ -> stmts
        compiledStmts <- traverse compile stmts'
        modify (\st -> st { localVars = prev_vars })
        return $ mconcat compiledStmts

instance Compilable Stmt where
    compile (SEmpty _) = pure $ singleton ""
    compile (SBlock _ block) = compile block
    compile (SExp _ expr) = fst <$> compileExpr expr
    compile (SIncr _ lval) = do
        (llvmCode', val) <- compileLVal lval
        let argType = case val of
                I32 _ -> " i32 "
                I1 _ -> " i1 "
                I8Ptr _ _ -> " i8* "
                Register _ -> " i32 "
                RegisterPtr _ -> " i32 "
        (loadCode, val') <- case val of
            RegisterPtr loc -> do
                loc2 <- gets currentLoc
                modify (\st -> st { currentLoc = loc2 + 1 })
                return (singleton $ show (Register loc2) ++ " = load " ++ argType ++ ", " ++ argType ++ "* " ++ show val ++ "\n", Register loc2)
            _ -> return (singleton "", val)
        let llvmCode = llvmCode' <> loadCode
        loc <- gets currentLoc
        modify (\st -> st { currentLoc = loc + 1 })
        return $ llvmCode <> singleton (show (Register loc) ++ " = add" ++ argType ++ show val' ++ ", 1\n") <>
            singleton ("store " ++ argType ++ " " ++ show (Register loc) ++ ", " ++ argType ++ "* " ++ show val ++ "\n")
    compile (SDecr _ lval) = do
        (llvmCode', val) <- compileLVal lval
        let argType = case val of
                I32 _ -> " i32 "
                I1 _ -> " i1 "
                I8Ptr _ _ -> " i8* "
                Register _ -> " i32 "
                RegisterPtr _ -> " i32 "
        (loadCode, val') <- case val of
            RegisterPtr loc -> do
                loc2 <- gets currentLoc
                modify (\st -> st { currentLoc = loc2 + 1 })
                return (singleton $ show (Register loc2) ++ " = load " ++ argType ++ ", " ++ argType ++ "* " ++ show val ++ "\n", Register loc2)
            _ -> return (singleton "", val)
        let llvmCode = llvmCode' <> loadCode
        loc <- gets currentLoc
        modify (\st -> st { currentLoc = loc + 1 })
        return $ llvmCode <> singleton (show (Register loc) ++ " = sub" ++ argType ++ show val' ++ ", 1\n") <>
            singleton ("store " ++ argType ++ " " ++ show (Register loc) ++ ", " ++ argType ++ "* " ++ show val ++ "\n")
    compile (SRetVoid _) = pure $ singleton "ret void\n"
    compile (SRetExp _ exp) = do
        env <- ask
        let llvmType = returnType env
        case llvmType of
            Nothing -> unsafePerformIO $ error "Internal compiler error: return type not set"
            Just llvmType -> do
                (llvmCode, valRaw) <- compileExpr exp
                (loadCode, val) <- case valRaw of
                    RegisterPtr loc -> do
                        loc2 <- gets currentLoc
                        modify (\st -> st { currentLoc = loc2 + 1 })
                        return (singleton $ show (Register loc2) ++ " = load " ++ llvmType ++ ", " ++ llvmType ++ "* " ++ show valRaw ++ "\n", Register loc2)
                    _ -> return (singleton "", valRaw)
                return $ llvmCode <> loadCode <> singleton ("ret " ++ llvmType ++ " " ++ show val ++ "\n")
    compile (SDecl _ decltype items) = do
        let llvmType = case decltype of
                TInt _ -> "i32"
                TStr _ -> "i8*"
                TBool _ -> "i1"
                TVoid _ -> error "Internal compiler error: void type in variable declaration"
        -- if DeclInit return expression, if DeclNoInit, return default value
        initExprs <- traverse (\case
            DeclInit _ (Ident name) expr -> do
                (llvmCode, valRaw) <- compileExpr expr
                (loadCode, val) <- case valRaw of
                    RegisterPtr loc -> do
                        loc2 <- gets currentLoc
                        modify (\st -> st { currentLoc = loc2 + 1 })
                        return (singleton $ show (Register loc2) ++ " = load " ++ llvmType ++ ", " ++ llvmType ++ "* " ++ show valRaw ++ "\n", Register loc2)
                    _ -> return (singleton "", valRaw)
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                modify (\st -> st { localVars = Data.Map.insert (Ident name) (RegisterPtr loc) (localVars st) })
                return $ llvmCode <> loadCode <> singleton ("%v" ++ show loc ++ " = alloca " ++ llvmType ++ "\n") <>
                    singleton ("store " ++ llvmType ++ " " ++ show val ++ ", " ++ llvmType ++ "* %v" ++ show loc ++ " ; just an ass\n")
            DeclNoInit _ (Ident name) -> do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                modify (\st -> st { localVars = Data.Map.insert (Ident name) (RegisterPtr loc) (localVars st) })
                return $ singleton $ "%v" ++ show loc ++ " = alloca " ++ llvmType ++ "\n"
            ) items
        return $ mconcat initExprs
        
    compile (SCondElse _ exp stmt1 stmt2) = do
        (llvmCode, valraw) <- compileExpr exp
        (loadCode, val) <- case valraw of
            RegisterPtr loc -> do
                loc2 <- gets currentLoc
                modify (\st -> st { currentLoc = loc2 + 1 })
                return (singleton $ show (Register loc2) ++ " = load i1, i1* " ++ show valraw ++ "\n", Register loc2)
            _ -> return (singleton "", valraw)
        if val == I1 True then do
            thenBlock <- compile stmt1
            return $ llvmCode <> thenBlock
        else if val == I1 False then do
            elseBlock <- compile stmt2
            return $ llvmCode <> elseBlock
        else do
            thenBlock <- compile stmt1
            elseBlock <- compile stmt2
            condTrueLabel <- gets currentLabel
            modify (\st -> st { currentLabel = condTrueLabel + 1 })
            condFalseLabel <- gets currentLabel
            modify (\st -> st { currentLabel = condFalseLabel + 1 })
            endLabel <- gets currentLabel
            modify (\st -> st { currentLabel = endLabel + 1 })
            return $ llvmCode <> loadCode <> singleton ("br i1 " ++ show val ++ ", label %condTrue" ++ show condTrueLabel ++ ", label %condFalse" ++ show condFalseLabel ++ "\n") <>
                singleton ("condTrue" ++ show condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label %condEnd" ++ show endLabel ++ "\n") <>
                singleton ("condFalse" ++ show condFalseLabel ++ ":\n") <> elseBlock <> singleton ("br label %condEnd" ++ show endLabel ++ "\n") <>
                singleton ("condEnd" ++ show endLabel ++ ":\n")
    compile (SCond _ exp stmt) = do
        (llvmCode, valraw) <- compileExpr exp
        (loadCode, val) <- case valraw of
            RegisterPtr loc -> do
                loc2 <- gets currentLoc
                modify (\st -> st { currentLoc = loc2 + 1 })
                return (singleton $ show (Register loc2) ++ " = load i1, i1* " ++ show valraw ++ "\n", Register loc2)
            _ -> return (singleton "", valraw)
        if val == I1 True then do
            thenBlock <- compile stmt
            return $ llvmCode <> thenBlock
        else if val == I1 False then do
            return llvmCode
        else do
            thenBlock <- compile stmt
            condTrueLabel <- gets currentLabel
            modify (\st -> st { currentLabel = condTrueLabel + 1 })
            condFalseLabel <- gets currentLabel
            modify (\st -> st { currentLabel = condFalseLabel + 1 })
            return $ llvmCode <> loadCode <> singleton ("br i1 " ++ show val ++ ", label %condTrue" ++ show condTrueLabel ++ ", label %condFalse" ++ show condFalseLabel ++ "\n") <>
                singleton ("condTrue" ++ show condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label %condFalse" ++ show condFalseLabel ++ "\n") <>
                singleton ("condFalse" ++ show condFalseLabel ++ ":\n")
    compile (SAss _ lval exp) = do
        (llvmCodeLVal, valLVal) <- compileLVal lval
        (llvmCodeExp, valExp) <- compileExpr exp
        let valExpType = case valExp of
                I32 _ -> "i32"
                I1 _ -> "i1"
                I8Ptr _ _ -> "i8*"
                Register _ -> "i32"
                RegisterPtr _ -> "i32"
        (valExp', loadCode) <- case valExp of
            RegisterPtr loc -> do
                loc2 <- gets currentLoc
                modify (\st -> st { currentLoc = loc2 + 1 })
                return (Register loc2, singleton $ show (Register loc2) ++ " = load " ++ valExpType ++ ", " ++ valExpType ++ "* " ++ show valExp ++ "\n")
            _ -> return (valExp, singleton "")
        let llvmCode = llvmCodeLVal <> llvmCodeExp <> loadCode
        case valLVal of
            RegisterPtr loc -> return $ llvmCode <> singleton ("store " ++ valExpType ++ " " ++ show valExp' ++ ", " ++ valExpType ++ "* " ++ show valLVal ++ " ; just an ass\n")
            _ -> error $ "Internal compiler error: lvalue is not a register:" ++ show valLVal
    compile (SWhile _ exp stmt) = do
        (llvmCode, val) <- compileExpr exp
        loopLabel <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabel + 1 })
        body <- compile stmt
        endLabel <- gets currentLabel
        modify (\st -> st { currentLabel = endLabel + 1 })
        return $ singleton ("br label %loop" ++ show loopLabel ++ "\nloop" ++ show loopLabel ++ ":\n") <>
            llvmCode <> singleton ("br i1 " ++ show val ++ ", label %loopBody" ++ show loopLabel ++ ", label %loopEnd" ++ show endLabel ++ "\n") <>
            singleton ("loopBody" ++ show loopLabel ++ ":\n") <> body <>
            singleton ("br label %loop" ++ show loopLabel ++ "\n") <>
            singleton ("loopEnd" ++ show endLabel ++ ":\n")



compileExpr :: Expr -> IM (Data.Sequence.Seq String, Value)
compileExpr (EApp _ (Ident ident) args) = do
    compiledRawArgs <- traverse compileExpr args
    -- if a value is a register pointer, load it
    compiledArgs <- traverse (\case
        (llvmCode, RegisterPtr loc) -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (llvmCode <> singleton (show (Register loc2) ++ " = load i32, i32* " ++ show (RegisterPtr loc) ++ "\n"), Register loc2)
        (llvmCode, val) -> return (llvmCode, val)
        ) compiledRawArgs
    let llvmCode = mconcat . map fst $ compiledArgs

    -- take function types from environment
    env <- ask
    let argTypesRaw = case Data.Map.lookup ident (functionArgTypes env) of
            Just types -> types
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"
    let argTypes = map (\case
            TInt _ -> "i32"
            TStr _ -> "i8*"
            TBool _ -> "i1"
            TVoid _ -> error "Internal compiler error: void type in function arguments"
            ) argTypesRaw
    let retTypeRaw = case Data.Map.lookup ident (functionRetTypes env) of
            Just type_ -> type_
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"
    let retType = case retTypeRaw of
            TInt _ -> "i32"
            TStr _ -> "i8*"
            TBool _ -> "i1"
            TVoid _ -> "void"
    
    
    let argVals = map snd compiledArgs
    -- add types to arguments
    let argsWithTypes = zip argTypes argVals
    let argsStr = Data.List.intercalate ", " $ map (\(argType, argVal) -> argType ++ " " ++ show argVal) argsWithTypes
    
    -- get new loc
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    if retType == "void" then
        return (llvmCode <> singleton ("call " ++ retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"), Register loc)
    else
        return (llvmCode <> singleton (show (Register loc)  ++ " = call " ++ retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"), Register loc)


compileExpr (ELVal _ lval) = compileLVal lval
compileExpr (ERel _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (llvmCode2, val2raw) <- compileExpr expr2
    let argType = case val1raw of
            I32 _ -> " i32 "
            I1 _ -> " i1 "
            I8Ptr _ _ -> " i8* "
            Register _ -> " i32 "
            RegisterPtr _ -> " i32 "
    (loadCode1, val1) <- case val1raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load " ++ argType ++ ", " ++ argType ++ "* " ++ show val1raw ++ "\n", Register loc2)
        _ -> return (singleton "", val1raw)
    (loadCode2, val2) <- case val2raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load " ++ argType ++ ", " ++ argType ++ "* " ++ show val2raw ++ "\n", Register loc2)
        _ -> return (singleton "", val2raw)
    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return (llvmCode <> singleton (show (Register loc) ++ " = icmp " ++ case op of
        OpLt _ -> "slt"
        OpLe _ -> "sle"
        OpGt _ -> "sgt"
        OpGe _ -> "sge"
        OpEq _ -> "eq"
        OpNe _ -> "ne"
        ++ argType ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc)
compileExpr (ENeg _ expr) = do
    (llvmCode, val) <- compileExpr expr
    let argType = case val of
            I32 _ -> " i32 "
            I1 _ -> " i1 "
            I8Ptr _ _ -> " i8* "
            Register _ -> " i32 "
            RegisterPtr _ -> " i32 "
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return (llvmCode <> singleton (show (Register loc) ++ " = sub" ++ argType ++ "0, " ++ show val ++ "; ENeg \n"), Register loc)
compileExpr (EAdd _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (llvmCode2, val2raw) <- compileExpr expr2
    let argType = case val1raw of
            I32 _ -> " i32 "
            I1 _ -> " i1 "
            I8Ptr _ _ -> " i8* "
            Register _ -> " i32 "
            RegisterPtr _ -> " i32 "
    (loadCode1, val1) <- case val1raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i32, i32* " ++ show val1raw ++ "\n", Register loc2)
        _ -> return (singleton "", val1raw)
    (loadCode2, val2) <- case val2raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i32, i32* " ++ show val2raw ++ "\n", Register loc2)
        _ -> return (singleton "", val2raw)
    
    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    case op of
        OpAdd _ -> return (llvmCode <> singleton (show (Register loc) ++ " = add" ++ argType ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc)
        OpSub _ -> return (llvmCode <> singleton (show (Register loc) ++ " = sub" ++ argType ++ show val1 ++ ", " ++ show val2 ++ "; EAdd\n"), Register loc)
compileExpr (EMul _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (llvmCode2, val2raw) <- compileExpr expr2
    (loadCode1, val1) <- case val1raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i32, i32* " ++ show val1raw ++ "\n", Register loc2)
        _ -> return (singleton "", val1raw)
    (loadCode2, val2) <- case val2raw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i32, i32* " ++ show val2raw ++ "\n", Register loc2)
        _ -> return (singleton "", val2raw)
    let argType = case val1 of
            I32 _ -> " i32 "
            I1 _ -> " i1 "
            I8Ptr _ _ -> " i8* "
            Register _ -> " i32 "
            RegisterPtr _ -> " i32 "
    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    case op of
        OpMul _ -> return (llvmCode <> singleton (show (Register loc) ++ " = mul" ++ argType ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc)
        OpDiv _ -> return (llvmCode <> singleton (show (Register loc) ++ " = sdiv" ++ argType ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc)
        OpMod _ -> return (llvmCode <> singleton (show (Register loc) ++ " = srem" ++ argType ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc)
compileExpr (ELitInt _ int) = pure (singleton "", I32 int)
compileExpr (EString _ str) = do
    ind <- addNewString str
    return (singleton "\n", I8Ptr ind (toInteger $ length str + 1))
compileExpr (ELitTrue _) = pure (singleton "", I1 True)
compileExpr (ELitFalse _) = pure (singleton "", I1 False)
compileExpr (ENot _ expr) = do
    (llvmCode, valraw) <- compileExpr expr
    (loadCode, val) <- case valraw of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i1, i1* " ++ show valraw ++ "\n", Register loc2)
        _ -> return (singleton "", valraw)
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return (llvmCode <> loadCode <> singleton (show (Register loc) ++ " = xor i1 "  ++ show val ++ ", 1\n"), Register loc)
compileExpr (EOr _ expr1 _ expr2) = do
    (code, val) <- compileExpr (ENot BNFC'NoPosition (EAnd BNFC'NoPosition (ENot BNFC'NoPosition expr1) (OpAnd BNFC'NoPosition) (ENot BNFC'NoPosition expr2)))
    return (code, val)
compileExpr (EAnd _ expr1 _ expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (loadCode1, val1') <- case val1 of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i1, i1* " ++ show val1 ++ "\n", Register loc2)
        _ -> return (singleton "", val1)
    labelAnd <- gets currentLabel
    modify (\st -> st { currentLabel = labelAnd + 1 })
    (llvmCode2, val2) <- compileExpr expr2
    (loadCode2, val2') <- case val2 of
        RegisterPtr loc -> do
            loc2 <- gets currentLoc
            modify (\st -> st { currentLoc = loc2 + 1 })
            return (singleton $ show (Register loc2) ++ " = load i1, i1* " ++ show val2 ++ "\n", Register loc2)
        _ -> return (singleton "", val2)
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    resultLoc <- gets currentLoc
    modify (\st -> st { currentLoc = resultLoc + 1 })
    return $ (
        llvmCode1 <> loadCode1 <> 
        singleton ("%v" ++ show loc ++ " = alloca i1\n") <>
        singleton ("br i1 " ++ show val1' ++ ", label %andCheckSecond" ++ show labelAnd ++ ", label %andFalse" ++ show labelAnd ++ "\n") <>
        singleton ("andCheckSecond" ++ show labelAnd ++ ":\n") <>
        llvmCode2 <> loadCode2 <>
        singleton ("br i1 " ++ show val2' ++ ", label %andTrue" ++ show labelAnd ++ ", label %andFalse" ++ show labelAnd ++ "\n") <>
        singleton ("andFalse" ++ show labelAnd ++ ":\n") <>
        singleton ("store i1 0, i1* %v" ++ show loc ++ "\n") <>
        singleton ("br label %andEnd" ++ show labelAnd ++ "\n") <>
        singleton ("andTrue" ++ show labelAnd ++ ":\n") <>
        singleton ("store i1 1, i1* %v" ++ show loc ++ "\n") <>
        singleton ("br label %andEnd" ++ show labelAnd ++ "\n") <>
        singleton ("andEnd" ++ show labelAnd ++ ":\n") <>
        singleton ("%v" ++ show resultLoc ++ " = load i1, i1* %v" ++ show loc ++ "\n")
        , Register resultLoc)


compileExpr (ENewArr _ type_ expr) = error "not implemented"
compileExpr (ENew _ type_) = error "not implemented"


getVarValue :: Ident -> IM Value
getVarValue ident = do
    env <- ask
    localVars <- gets localVars
    case Data.Map.lookup ident (var env) of
        Just val -> return val
        Nothing -> case Data.Map.lookup ident localVars of
            Just val -> return val
            Nothing -> error $ "Internal compiler error: variable " ++ show ident ++ " not found"


-- it returns a register containing the address of the lvalue
compileLVal :: LVal -> IM (Data.Sequence.Seq String, Value)
compileLVal (LVar _ (Ident ident)) = do
    env <- ask
    varValue <- getVarValue (Ident ident)
    return (singleton "", varValue)
compileLVal (LArrAcc _ expr1 expr2) = error "not implemented"
compileLVal (LAttrAcc _ expr (Ident ident)) = error "not implemented"
