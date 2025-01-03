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

data Value = Register Integer | I32 Integer | I1 Bool | I8Ptr Integer Integer
instance Show Value where
    show (Register i) = "%v" ++ show i
    show (I32 i) = show i
    show (I1 b) = show b
    show (I8Ptr ind length) = "getelementptr inbounds([" ++ show length ++ " x i8], [" ++ show length ++ "x i8]* @strings" ++ show ind ++ ", i32 0, i32 0)"

data St = St {
    strings :: Map String Integer,
    currentLoc :: Integer,
    currentResult :: Value
}
initState :: St
initState = St {
    strings = Data.Map.empty,
    currentLoc = 0,
    currentResult = Register 0
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
        loadArgs <- mconcat . map singleton <$> traverse (\(Arg _ type_ (Ident name)) -> do
                llvmType <- concat . toList <$> compile type_
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                return $ "%v" ++ show loc ++ " = alloca " ++ llvmType ++ "\n" ++
                    "store " ++ llvmType ++ " %" ++ name ++ ", " ++ llvmType ++ "* %" ++ show loc
                ) args
        body <- local (\env -> env { returnType = Just llvmType }) $ do
            compile block
        return $ header <> loadArgs <> body <> Data.Sequence.singleton "\n}\n"

instance Compilable BlockC where
    compile (Block _ stmts) = do
        compiledStmts <- traverse compile stmts
        return $ mconcat compiledStmts

instance Compilable Stmt where
    compile (SEmpty _) = error "not implemented"
    compile (SBlock _ block) = compile block
    compile (SExp _ expr) = fst <$> compileExpr expr
    compile (SIncr _ expr) = error "not implemented"
    compile (SDecr _ expr) = error "not implemented"
    compile (SRetVoid _) = pure $ singleton "ret void\n"
    compile (SRetExp _ exp) = do
        env <- ask
        let llvmType = returnType env
        case llvmType of
            Nothing -> unsafePerformIO $ error "Internal compiler error: return type not set"
            Just llvmType -> do
                (llvmCode, val) <- compileExpr exp
                return $ llvmCode <> singleton ("ret " ++ llvmType ++ " " ++ show val ++ "\n")
    compile (SDecl _ decltype items) = error "not implemented"
    compile (SCondElse _ exp stmt1 stmt2) = error "not implemented"
    compile (SCond _ exp stmt) = error "not implemented"
    compile (SAss _ lval exp) = error "not implemented"
    compile (SWhile _ exp stmt) = error "not implemented"


compileExpr :: Expr -> IM (Data.Sequence.Seq String, Value)
compileExpr (EApp _ (Ident ident) args) = do
    compiledArgs <- traverse compileExpr args
    let llvmCode = mconcat . map fst $ compiledArgs
    let argVals = map snd compiledArgs
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


compileExpr (ELVal _ lval) = error "not implemented"
compileExpr (ERel _ expr1 op expr2) = error "not implemented"
compileExpr (ENeg _ expr) = error "not implemented"
compileExpr (EAdd _ expr1 op expr2) = error "not implemented"
compileExpr (EMul _ expr1 op expr2) = error "not implemented"
compileExpr (ELitInt _ int) = pure (singleton "", I32 int)
compileExpr (EString _ str) = do
    ind <- addNewString str
    return (singleton "\n", I8Ptr ind (toInteger $ length str + 1))
compileExpr (ELitTrue _) = pure (singleton "", I1 True)
compileExpr (ELitFalse _) = pure (singleton "", I1 False)
compileExpr (ENot _ expr) = error "not implemented"
compileExpr (EOr _ expr1 _ expr2) = error "not implemented"
compileExpr (EAnd _ expr1 _ expr2) = error "not implemented"
compileExpr (ENewArr _ type_ expr) = error "not implemented"
compileExpr (ENew _ type_) = error "not implemented"



