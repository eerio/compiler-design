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

data PrimitiveType =
    VoidType
    | I8Type
    | I32Type
    | I1Type
    | StructType [PrimitiveType]
    | PointerType PrimitiveType
    deriving (Eq)

data Primitive =
    I1 Bool
    | I8 Integer
    | I32 Integer
    | Struct [Primitive]
    | Pointer Primitive
    deriving (Eq)

data Value =
    ConstValue Primitive
    | StringLiteral Integer Integer
    | Register Integer PrimitiveType
    deriving (Eq)

instance Show Primitive where
    show (I1 True) = "true"
    show (I1 False) = "false"
    show (I8 i) = show i
    show (I32 i) = show i
    show (Struct fields) = "{" ++ Data.List.intercalate ", " (map show fields) ++ "}"
    show (Pointer p) = show p ++ "*"

instance Show Value where
    show (ConstValue p) = show p
    show (Register loc _) = "%v" ++ show loc
    show (StringLiteral ind length) = "getelementptr inbounds([" ++ show length ++ " x i8], [" ++ show length ++ "x i8]* @strings" ++ show ind ++ ", i32 0, i32 0)"

class LLVMTypeable a where
    llvmType :: a -> PrimitiveType

instance LLVMTypeable Primitive where
    llvmType (I1 _) = I1Type
    llvmType (I8 _) = I8Type
    llvmType (I32 _) = I32Type
    llvmType (Struct fields) = StructType $ map llvmType fields
    llvmType (Pointer p) = PointerType $ llvmType p

instance LLVMTypeable Value where
    llvmType (ConstValue p) = llvmType p
    llvmType (StringLiteral _ _) = PointerType I8Type
    llvmType (Register _ p) = p

instance LLVMTypeable (Type' BNFC'Position) where
    llvmType (TInt _) = I32Type
    llvmType (TStr _) = PointerType I8Type
    llvmType (TBool _) = I1Type
    llvmType (TVoid _) = VoidType

instance Show PrimitiveType where
    show I1Type = "i1"
    show I8Type = "i8"
    show I32Type = "i32"
    show (StructType fields) = "{" ++ Data.List.intercalate ", " (map show fields) ++ "}"
    show (PointerType p) = show p ++ "*"
    show VoidType = "void"

data St = St {
    strings :: Map String Integer,
    currentLoc :: Integer,
    currentLabel :: Integer,
    localVars :: Map Ident Value
}
initState :: St
initState = St {
    strings = Data.Map.empty,
    currentLoc = 0,
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
    returnType :: Maybe PrimitiveType,
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
    compile (FunDef _ retType_ (Ident name) args block) = do
        let retType = llvmType retType_
        argsCompiled <- toList . mconcat <$> traverse compile args
        let argsStr = Data.List.intercalate ", " argsCompiled
        let header = Data.Sequence.singleton $ unlines [
                "define " ++ show retType ++ " @" ++ name ++ "(" ++ argsStr ++ ") {"
                ]
        initLoc <- gets currentLoc
        varLocs <- traverse (\(Arg _ type_ (Ident name)) -> do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                return (Ident name, Register loc (PointerType $ llvmType type_))
                ) args
        modify (\st -> st { currentLoc = initLoc })
        loadArgs <- mconcat . map singleton <$> traverse (\(Arg _ type_ (Ident name)) -> do
                let llvmTypeArg = llvmType type_
                let llvmTypeReg = PointerType llvmTypeArg
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let register = Register loc llvmTypeReg
                return $ show register ++ " = alloca " ++ show llvmTypeArg ++ "\n" ++
                    "store " ++ show llvmTypeArg ++ " %" ++ name ++ ", " ++ show llvmTypeReg  ++ " " ++ show register ++ " ; already loaded\n"
                ) args
        let newVars = Data.Map.fromList varLocs
        body <- local (\env -> env { returnType = Just retType, var = newVars }) $ do
            compile block
        return $ header <> loadArgs <> body <> Data.Sequence.singleton "\n}\n"

instance Compilable BlockC where
    compile (Block _ []) = do
        env <- ask
        let retStmt = case returnType env of
                Just VoidType -> SRetVoid BNFC'NoPosition
                Just I32Type -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                Just I1Type -> SRetExp BNFC'NoPosition (ELitFalse BNFC'NoPosition)
                Just (PointerType p) -> error "Internal compiler error: returning pointer"
                Nothing -> error "Internal compiler error: no return type"
        compile retStmt

    compile (Block _ stmts) = do
        prev_vars <- gets localVars
        -- if block ends with cond or cond else, add dummy ret after it
        env <- ask
        let retStmt = case returnType env of
                Just VoidType -> SRetVoid BNFC'NoPosition
                Just I32Type -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                Just I1Type -> SRetExp BNFC'NoPosition (ELitFalse BNFC'NoPosition)
                Just (PointerType p) -> error "Internal compiler error: returning pointer"
                Nothing -> error "Internal compiler error: no return type"

        let stmts' = case last stmts of
                SRetExp {} -> stmts
                SRetVoid {} -> stmts
                _ -> stmts ++ [retStmt]
        compiledStmts <- traverse compile stmts'
        modify (\st -> st { localVars = prev_vars })
        return $ mconcat compiledStmts

dereferenceIfNeed :: Value -> IM (Data.Sequence.Seq String, Value)
dereferenceIfNeed val = pure (singleton "", val)

dereference :: Value -> IM (Data.Sequence.Seq String, Value)
dereference val = case val of
    reg@(Register loc (PointerType p)) -> do
        loc2 <- gets currentLoc
        modify (\st -> st { currentLoc = loc2 + 1 })
        let returnReg = Register loc2 p
        return (singleton (show returnReg ++ " = load " ++ show p ++ ", " ++ show (PointerType p) ++ " " ++ show reg ++ "\n"), returnReg)
    _ -> error "Internal compiler error: trying to dereference non-pointer"

compileBinOp :: PrimitiveType -> Value -> Value -> String -> IM (Data.Sequence.Seq String, Value)
compileBinOp type_ val1 val2 op = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc type_
    return (singleton (show returnReg ++ " = " ++ op ++ " " ++ show type_ ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n"), returnReg)

instance Compilable Stmt where
    compile (SEmpty _) = pure $ singleton ""
    compile (SBlock _ block) = compile block
    compile (SExp _ expr) = fst <$> compileExpr expr
    compile (SIncr _ lval) = do
        (llvmCode, val) <- compileLVal lval
        (loadCode, valLoaded) <- dereference val
        (incrCode, incrVal) <- compileBinOp (llvmType valLoaded) valLoaded (ConstValue (I32 1)) "add"
        return $ llvmCode <> loadCode <> incrCode <> singleton ("store i32 " ++ show incrVal ++ ", i32* " ++ show val ++ "\n")
    compile (SDecr _ lval) = do
        (llvmCode, val) <- compileLVal lval
        (loadCode, valLoaded) <- dereference val
        (decrCode, decrVal) <- compileBinOp (llvmType valLoaded) valLoaded (ConstValue (I32 1)) "sub"
        return $ llvmCode <> loadCode <> decrCode <> singleton ("store i32 " ++ show decrVal ++ ", i32* " ++ show val ++ "\n")
    compile (SRetVoid _) = pure $ singleton "ret void\n"
    compile (SRetExp _ exp) = do
        (llvmCode, val) <- compileExpr exp
        (loadCode, valLoaded) <- dereferenceIfNeed val
        return $ llvmCode <> loadCode <> singleton ("ret " ++ show (llvmType valLoaded) ++ " " ++ show valLoaded ++ "\n")
    compile (SDecl _ decltype items) = do
        initExprs <- traverse declareItem items
        return $ mconcat initExprs
        where
            type_ = llvmType decltype

            declareItem :: DeclItem' BNFC'Position -> IM (Data.Sequence.Seq String)
            declareItem (DeclInit _ (Ident name) expr) = do
                (llvmCode, valRaw) <- compileExpr expr
                (loadCode, val) <- dereferenceIfNeed valRaw
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let regType = PointerType type_
                let reg = Register loc regType
                modify (\st -> st { localVars = Data.Map.insert (Ident name) reg (localVars st) })
                return $ llvmCode <> loadCode <> singleton ("%v" ++ show loc ++ " = alloca " ++ show type_ ++ "\n") <>
                    singleton ("store " ++ show type_ ++ " " ++ show val ++ ", " ++ show regType ++ " " ++ show reg ++ " ; declaration\n")
            declareItem (DeclNoInit _ (Ident name)) = do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let regType = PointerType $ type_
                let reg = Register loc regType
                modify (\st -> st { localVars = Data.Map.insert (Ident name) reg (localVars st) })
                return $ singleton ("%v" ++ show loc ++ " = alloca " ++ show type_ ++ "\n")

    compile (SCondElse _ exp stmt1 stmt2) = do
        (llvmCode, valraw) <- compileExpr exp
        (loadCode, val) <- dereferenceIfNeed valraw
        thenBlock <- compile stmt1
        elseBlock <- compile stmt2
        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let condFalseLabel = "%condFalse" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN
        return $ llvmCode <> loadCode <> singleton ("br i1 " ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ condFalseLabel ++ "\n") <>
            singleton (tail condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail condFalseLabel ++ ":\n") <> elseBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")
    compile (SCond _ exp stmt) = do
        (llvmCode, valraw) <- compileExpr exp
        (loadCode, val) <- dereferenceIfNeed valraw
        thenBlock <- compile stmt
        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN
        return $ llvmCode <> loadCode <> singleton ("br i1 " ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ endLabel ++ "\n") <>
            singleton (tail condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")
    compile (SAss _ lval exp) = do
        (llvmCodeLVal, valLVal) <- compileLVal lval
        (llvmCodeExp, valExp) <- compileExpr exp
        (loadCode, valExp') <- dereferenceIfNeed valExp
        let valExpType = llvmType valExp'
        return $ llvmCodeLVal <> llvmCodeExp <> loadCode <> singleton ("store " ++ show valExpType ++ " " ++ show valExp' ++ ", " ++ show (PointerType valExpType) ++ " " ++ show valLVal ++ "\n")
    compile (SWhile _ exp stmt) = do
        (llvmCode, val) <- compileExpr exp
        (loadCode, valLoaded) <- dereferenceIfNeed val
        loopLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabelN + 1 })
        let condLabel = "%loopCond" ++ show loopLabelN
        let loopLabel = "%loop" ++ show loopLabelN
        let endLabel = "%loopEnd" ++ show loopLabelN
        body <- compile stmt
        return $ singleton ("br label " ++ condLabel ++ "\n") <>
            singleton (tail condLabel ++ ":\n") <> llvmCode <> loadCode <> singleton ("br i1 " ++ show valLoaded ++ ", label " ++ loopLabel ++ ", label " ++ endLabel ++ "\n") <>
            singleton (tail loopLabel ++ ":\n") <> 
            body <> singleton ("br label " ++ condLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")

compileExpr :: Expr -> IM (Data.Sequence.Seq String, Value)
compileExpr (EApp _ (Ident ident) args) = do
    compiledArgs <- traverse (\expr -> do
            (llvmCode, val) <- compileExpr expr
            (loadCode, valLoaded) <- dereferenceIfNeed val
            return (llvmCode <> loadCode, valLoaded)
            ) args
    let llvmCode = mconcat . map fst $ compiledArgs
    -- take function types from environment
    env <- ask
    let argTypesRaw = case Data.Map.lookup ident (functionArgTypes env) of
            Just types -> types
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"
    let argTypes = map llvmType argTypesRaw
    let retTypeRaw = case Data.Map.lookup ident (functionRetTypes env) of
            Just type_ -> type_
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"
    let retType = llvmType retTypeRaw

    let argVals = map snd compiledArgs
    -- add types to arguments
    let argsWithTypes = zip argTypes argVals
    let argsStr = Data.List.intercalate ", " $ map (\(argType, argVal) -> show argType ++ " " ++ show argVal) argsWithTypes

    -- get new loc
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnRegister = Register loc retType
    case retType of
        VoidType -> return (llvmCode <> singleton ("call " ++ show retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"), Register loc VoidType)
        _ -> return (llvmCode <> singleton (show returnRegister ++ " = call " ++ show retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"), returnRegister)

compileExpr (ELVal _ lval) = do
    (llvmCode, val) <- compileLVal lval
    (loadCode, valLoaded) <- dereference val
    return (llvmCode <> loadCode, valLoaded)

compileExpr (ERel _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (loadCode1, val1) <- dereferenceIfNeed val1raw
    (llvmCode2, val2raw) <- compileExpr expr2
    (loadCode2, val2) <- dereferenceIfNeed val2raw
    let argType = llvmType val1
    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return (llvmCode <> singleton (show (Register loc I1Type) ++ " = icmp " ++ case op of
        OpLt _ -> "slt"
        OpLe _ -> "sle"
        OpGt _ -> "sgt"
        OpGe _ -> "sge"
        OpEq _ -> "eq"
        OpNe _ -> "ne"
        ++ " " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n"), Register loc I1Type)

compileExpr (ENeg _ expr) = do
    (llvmCode, val) <- compileExpr expr
    let argType = llvmType val
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return (llvmCode <> singleton (show (Register loc argType) ++ " = sub " ++ show argType ++ " 0, " ++ show val ++ "; ENeg \n"), Register loc argType)
compileExpr (EAdd _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (loadCode1, val1) <- dereferenceIfNeed val1raw
    (llvmCode2, val2raw) <- compileExpr expr2
    (loadCode2, val2) <- dereferenceIfNeed val2raw
    let argType = llvmType val1

    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc argType
    case op of
        OpAdd _ -> return (llvmCode <> singleton (show returnReg ++ " = add " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EAdd\n"), returnReg)
        OpSub _ -> return (llvmCode <> singleton (show returnReg ++ " = sub " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; ESub\n"), returnReg)
compileExpr (EMul _ expr1 op expr2) = do
    (llvmCode1, val1raw) <- compileExpr expr1
    (llvmCode2, val2raw) <- compileExpr expr2
    (loadCode1, val1) <- dereferenceIfNeed val1raw
    (loadCode2, val2) <- dereferenceIfNeed val2raw
    let argType = llvmType val1
    let llvmCode = llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc argType
    case op of
        OpMul _ -> return (llvmCode <> singleton (show returnReg ++ " = mul " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EMul\n"), returnReg)
        OpDiv _ -> return (llvmCode <> singleton (show returnReg ++ " = sdiv " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EDiv\n"), returnReg)
        OpMod _ -> return (llvmCode <> singleton (show returnReg ++ " = srem " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EMod\n"), returnReg)

compileExpr (ELitInt _ int) = pure (singleton "", ConstValue (I32 int))
compileExpr (EString _ str) = do
    ind <- addNewString str
    return (singleton "\n", StringLiteral ind (toInteger $ length str + 1))
compileExpr (ELitTrue _) = pure (singleton "", ConstValue (I1 True))
compileExpr (ELitFalse _) = pure (singleton "", ConstValue (I1 False))
compileExpr (ENot _ expr) = do
    (llvmCode, valraw) <- compileExpr expr
    (loadCode, val) <- dereferenceIfNeed valraw
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc I1Type
    return (llvmCode <> loadCode <> singleton (show returnReg ++ " = xor i1 1, " ++ show val ++ "\n"), returnReg)
compileExpr (EOr _ expr1 _ expr2) = do
    (code, val) <- compileExpr (ENot BNFC'NoPosition (EAnd BNFC'NoPosition (ENot BNFC'NoPosition expr1) (OpAnd BNFC'NoPosition) (ENot BNFC'NoPosition expr2)))
    return (code, val)
compileExpr (EAnd _ expr1 _ expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (loadCode1, val1') <- dereferenceIfNeed val1
    labelAnd <- gets currentLabel
    modify (\st -> st { currentLabel = labelAnd + 1 })
    (llvmCode2, val2) <- compileExpr expr2
    (loadCode2, val2') <- dereferenceIfNeed val2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    resultLoc <- gets currentLoc
    modify (\st -> st { currentLoc = resultLoc + 1 })
    let labelCheckSecond = "%andCheckSecond" ++ show labelAnd
    let labelFalse = "%andFalse" ++ show labelAnd
    let labelTrue = "%andTrue" ++ show labelAnd
    let labelEnd = "%andEnd" ++ show labelAnd
    let returnRegPtr = Register loc (PointerType I1Type)
    let returnReg = Register resultLoc I1Type
    return (
        llvmCode1 <> loadCode1 <>
        singleton (show returnRegPtr ++ " = alloca i1\n") <>
        singleton ("br i1 " ++ show val1' ++ ", label " ++ labelCheckSecond ++ ", label " ++ labelFalse ++ "\n") <>
        singleton (tail labelCheckSecond ++ ":\n") <>
        llvmCode2 <> loadCode2 <>
        singleton ("br i1 " ++ show val2' ++ ", label " ++ labelTrue ++ ", label " ++ labelFalse ++ "\n") <>
        singleton (tail labelFalse ++ ":\n") <>
        singleton ("store i1 0, i1* " ++ show returnRegPtr ++ "\n") <>
        singleton ("br label " ++ labelEnd ++ "\n") <>
        singleton (tail labelTrue ++ ":\n") <>
        singleton ("store i1 1, i1* " ++ show returnRegPtr ++ "\n") <>
        singleton ("br label " ++ labelEnd ++ "\n") <>
        singleton (tail labelEnd ++ ":\n") <>
        singleton (show returnReg ++ " = load i1, i1* " ++ show returnRegPtr ++ "\n")
        , returnReg)

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
