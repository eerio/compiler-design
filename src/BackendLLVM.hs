{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
import Data.Maybe (Maybe, fromMaybe, maybeToList)
import Data.Foldable (toList)
import Data.Char(ord)
import Numeric(showHex)
import Text.ParserCombinators.ReadP (char)
import Data.Graph (Graph, Vertex, graphFromEdges, topSort)


newtype Label = Label Integer
    deriving (Eq)

newtype VarName = VarName Integer
    deriving (Eq)

newtype Var = Var (VarName, PrimitiveType)
    deriving (Eq)

data PrimitiveType =
    VoidType
    | I8Type
    | I32Type
    | I1Type
    | PointerType PrimitiveType
    | FunctionType PrimitiveType [PrimitiveType]
    | ClassType Ident
    | ClassVtableType Ident
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
    llvmType (TCls _ (Ident name)) = PointerType $ ClassType (Ident name)
    llvmType (TFun _ retType argTypes) = FunctionType (llvmType retType) (map llvmType argTypes)

instance LLVMTypeable (FunDefC' BNFC'Position) where
    llvmType (FunDef _ retType _ args _) = do
        let argTypes = map (\(Arg _ type_ _) -> llvmType type_) args
        PointerType $ FunctionType (llvmType retType) argTypes

instance Show PrimitiveType where
    show I1Type = "i1"
    show I8Type = "i8"
    show I32Type = "i32"
    show (PointerType p) = show p ++ "*"
    show VoidType = "void"
    show (FunctionType retType argTypes) = show retType ++ " (" ++ Data.List.intercalate ", " (map show argTypes) ++ ")"
    show (ClassType (Ident name)) = "%class." ++ name
    show (ClassVtableType (Ident name)) = "%vtable." ++ name ++ ".type"


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

data Class = Class {
    parent :: Maybe Ident,
    fields :: [(Ident, PrimitiveType)],
    methods :: [(Ident, PrimitiveType)]
} deriving (Show)

classSize :: Class -> Integer
classSize cls = do
    let fields' = fields cls
    8 + 8 * toInteger (length fields')

processClass :: Map Ident Class -> ClsDefC -> Map Ident Class
processClass acc cls = 
    let inheritedFields  = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . fields)) (getParentName cls)
        inheritedMethods = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . methods)) (getParentName cls)
        newClass = Class (getParentName cls) (inheritedFields ++ getAttrTypes cls) (inheritedMethods ++ getMethodTypes cls)
    in Data.Map.insert (getClassName cls) newClass acc

getClassName :: ClsDefC -> Ident
getClassName (ClsDef _ ident _) = ident
getClassName (ClsDefExt _ ident _ _) = ident

getParentName :: ClsDefC -> Maybe Ident
getParentName (ClsDef _ _ _) = Nothing
getParentName (ClsDefExt _ _ ident _) = Just ident

createClassMap :: [ClsDefC] -> Map Ident Class
createClassMap clsDefs = 
    let (graph, nodeFromVertex, _) = graphFromEdges [(cls, getClassName cls, maybeToList (getParentName cls)) | cls <- clsDefs]
        sortedVertices = topSort graph
        sortedClasses = map (\v -> let (cls, _, _) = nodeFromVertex v in cls) sortedVertices
    in foldl processClass Data.Map.empty sortedClasses


data Env = Env {
    var :: Map Ident Value,
    returnType :: Maybe PrimitiveType,
    functionRetTypes :: Map String (Type' BNFC'Position),
    functionArgTypes :: Map String [Type' BNFC'Position],
    classes :: Map Ident Class
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

filterCls :: [TopDefC] -> [ClsDefC]
filterCls = foldr f [] where
    f :: TopDefC -> [ClsDefC] -> [ClsDefC]
    f (ClsDefTop _ clsdef) acc = clsdef : acc
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

charToHex :: Char -> String
charToHex c = do
    let hex = showHex (ord c) ""
    if length hex == 1 then "\\0" ++ hex else "\\" ++ hex

instance Compilable ProgramC where
    compile (Program _ topDefs) = do
        let initCode = Data.Sequence.singleton $ unlines [
                "declare void @printInt(i32)",
                "declare void @printString(i8*)",
                "declare void @error()",
                "declare i32 @readInt()",
                "declare i8* @readString()",
                "declare i8* @__internal_concat(i8*, i8*)",
                "declare i8* @__calloc(i32)"
                ]

        indexOfField <- foldr Data.Map.union Data.Map.empty <$> traverse createIndexOfField (filterCls topDefs)
        indexOfMethod <- foldr Data.Map.union Data.Map.empty <$> traverse createIndexOfMethod (filterCls topDefs)
        env' <- ask
        let env = env' { classes = createClassMap (filterCls topDefs) }
        compiledTopDefs <- traverse (local (const env) . compile) topDefs
        -- compiledTopDefs <- traverse compile topDefs
        let code = mconcat compiledTopDefs
        allStrings <- gets strings
        -- change string to hex encoding
        let prepString rawStr = "\"" ++ concatMap charToHex rawStr ++ "\\00\""
        let llvmStrings = unlines $ map (\(str, ind) -> "@strings" ++ show ind ++ " = private constant [" ++ show (length str + 1) ++ " x i8] c" ++ prepString str ++ "\n") $ Data.Map.toList allStrings
        let vtables = mconcat <$> traverse createVtable (filterCls topDefs)
        return $ initCode <> singleton llvmStrings <> code

instance Compilable TopDefC where
    compile (FunDefTop _ def) = compile def
    compile (ClsDefTop _ def) = compile def

getArgType :: ArgC -> Type
getArgType (Arg _ t _) = t

getMemberType :: ClsMemDeclC -> [(Ident, Type)]
getMemberType (ClsMthdDecl _ (FunDef _ retType ident args _)) = [(ident, TFun BNFC'NoPosition retType (map getArgType args))]
getMemberType (ClsAttrDecl _ t items) = map (\(AttrItem _ ident) -> (ident, t)) items

getAttrType :: ClsMemDeclC -> [(Ident, PrimitiveType)]
getAttrType (ClsMthdDecl _ _) = []
getAttrType (ClsAttrDecl _ t items) = map (\(AttrItem _ ident) -> (ident, llvmType t)) items

getAttrTypes :: ClsDefC -> [(Ident, PrimitiveType)]
getAttrTypes (ClsDef _ _ mems) = concatMap getAttrType mems
getAttrTypes (ClsDefExt _ _ _ mems) = concatMap getAttrType mems

addSelfArgument :: Ident -> FunDefC -> FunDefC
addSelfArgument (Ident clsName) (FunDef pos retType ident args block) = FunDef pos retType ident (Arg pos (TCls pos (Ident clsName)) (Ident "self") : args) block

getMethodType :: Ident -> ClsMemDeclC -> [(Ident, PrimitiveType)]
getMethodType cls@(Ident iden) (ClsMthdDecl _ mt@(FunDef _ retType (Ident funiden) args _)) = do
    let withSelf = addSelfArgument cls mt
    [(Ident funiden, llvmType withSelf)]
getMethodType _ (ClsAttrDecl {}) = []

getMethodTypes :: ClsDefC -> [(Ident, PrimitiveType)]
getMethodTypes (ClsDef _ ident mems) = concatMap (getMethodType ident) mems
getMethodTypes (ClsDefExt _ ident _ mems) = concatMap (getMethodType ident) mems

createVtable :: ClsDefC -> IM (Data.Sequence.Seq String)
createVtable cls@(ClsDef _ (Ident clsName) mems) = do
    let methods = getMethodTypes cls
    let vtableType = "%vtable." ++ clsName ++ ".type = type { " ++ Data.List.intercalate ", " (map (show . snd) methods) ++ " }\n"
    let vtable = "@vtable." ++ clsName ++ " = global %vtable." ++ clsName ++ ".type { " ++ Data.List.intercalate ", " (map f methods) ++ " }\n"
    return $ singleton vtableType <> singleton vtable
    where
        f ((Ident ident), type_) = show type_ ++ " " ++ "@" ++ clsName ++ "_" ++ ident
createVtable cls@(ClsDefExt _ (Ident clsName) _ mems) = do
    let methods = getMethodTypes cls
    let vtableType = "%vtable." ++ clsName ++ ".type = type { " ++ Data.List.intercalate ", " (map (show . snd) methods) ++ " }\n"
    let vtable = "@vtable." ++ clsName ++ " = global %vtable." ++ clsName ++ ".type { " ++ Data.List.intercalate ", " (map f methods) ++ " }\n"
    return $ singleton vtableType <> singleton vtable
    where
        f ((Ident ident), type_) = show type_ ++ " " ++ "@" ++ clsName ++ "_" ++ ident


createIndexOfField :: ClsDefC -> IM (Map Ident Integer)
createIndexOfField cls@(ClsDef _ (Ident clsName) mems) = do
    let attrs = getAttrTypes cls
    let attrNames = map fst attrs
    return $ Data.Map.fromList $ zip attrNames [0..]
createIndexOfField cls@(ClsDefExt _ (Ident clsName) (Ident parent) mems) = do
    let attrs = getAttrTypes cls
    let attrNames = map fst attrs
    return $ Data.Map.fromList $ zip attrNames [0..]

createIndexOfMethod :: ClsDefC -> IM (Map Ident Integer)
createIndexOfMethod cls@(ClsDef _ (Ident clsName) mems) = do
    let methods = getMethodTypes cls
    let methodNames = map fst methods
    return $ Data.Map.fromList $ zip methodNames [0..]
createIndexOfMethod cls@(ClsDefExt _ (Ident clsName) (Ident parent) mems) = do
    let methods = getMethodTypes cls
    let methodNames = map fst methods
    return $ Data.Map.fromList $ zip methodNames [0..]

instance Compilable ClsDefC where
    compile c@(ClsDef _ (Ident nam) mems) = do
        vtable <- createVtable c
        let structName = "%class." ++ nam
        let vtable_ptr = ["%vtable." ++ nam ++ ".type*"]
        let members = getAttrTypes c
        let structDecl = unlines [
                structName ++ " = type { ",
                Data.List.intercalate ", " (vtable_ptr ++ map (show . snd) members),
                "}"
                ]
        return $ vtable <> singleton structDecl
    compile c@(ClsDefExt _ (Ident nam) (Ident parent) mems) = do
        vtable <- createVtable c
        let structName = "%class." ++ nam
        let vtable_ptr = ["%vtable." ++ nam ++ ".type*"]
        let members = getAttrTypes c
        let structDecl = unlines [
                structName ++ " = type { ",
                Data.List.intercalate ", " (vtable_ptr ++ map (show . snd) members),
                "}"
                ]
        return $ vtable <> singleton structDecl


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
    compile (FunDef _ retType_ (Ident name) args block@(Block _ stmts)) = do
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

        let retStmt = case retType of
                VoidType -> SRetVoid BNFC'NoPosition
                I32Type -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                I1Type -> SRetExp BNFC'NoPosition (ELitFalse BNFC'NoPosition)
                PointerType p -> SRetExp BNFC'NoPosition (EString BNFC'NoPosition "")
                _ -> error "Internal compiler error: no return type"
        let block' = Block BNFC'NoPosition (stmts ++ [retStmt])

        body <- local (\env -> env { returnType = Just retType, var = newVars }) $ do
            compile block'
        return $ header <> loadArgs <> body <> Data.Sequence.singleton "\n}\n"

instance Compilable BlockC where
    compile (Block _ []) = do
        env <- ask
        let retStmt = case returnType env of
                Just VoidType -> SRetVoid BNFC'NoPosition
                Just I32Type -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                Just I1Type -> SRetExp BNFC'NoPosition (ELitFalse BNFC'NoPosition)
                Just (PointerType p) -> SRetExp BNFC'NoPosition (EString BNFC'NoPosition "")
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
                Just (PointerType p) -> SRetExp BNFC'NoPosition (EString BNFC'NoPosition "")
                Nothing -> error "Internal compiler error: no return type"

        compiledStmts <- traverse compile stmts
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
        return $ llvmCode <> singleton ("ret " ++ show (llvmType val) ++ " " ++ show val ++ "\n")
    compile (SDecl _ decltype items) = do
        initExprs <- traverse declareItem items
        return $ mconcat initExprs
        where
            type_ = llvmType decltype

            declareItem :: DeclItem' BNFC'Position -> IM (Data.Sequence.Seq String)
            declareItem (DeclInit _ (Ident name) expr) = do
                (llvmCode, val) <- compileExpr expr
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let regType = PointerType type_
                let reg = Register loc regType
                modify (\st -> st { localVars = Data.Map.insert (Ident name) reg (localVars st) })
                return $ llvmCode <> singleton ("%v" ++ show loc ++ " = alloca " ++ show type_ ++ "\n") <>
                    singleton ("store " ++ show type_ ++ " " ++ show val ++ ", " ++ show regType ++ " " ++ show reg ++ " ; declaration\n")
            declareItem (DeclNoInit _ (Ident name)) = do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let regType = PointerType type_
                let reg = Register loc regType
                modify (\st -> st { localVars = Data.Map.insert (Ident name) reg (localVars st) })
                return $ singleton ("%v" ++ show loc ++ " = alloca " ++ show type_ ++ "\n")

    compile (SCondElse _ exp stmt1 stmt2) = do
        (llvmCode, val) <- compileExpr exp
        thenBlock <- compile stmt1
        elseBlock <- compile stmt2
        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let condFalseLabel = "%condFalse" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN
        return $ llvmCode <> singleton ("br i1 " ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ condFalseLabel ++ "\n") <>
            singleton (tail condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail condFalseLabel ++ ":\n") <> elseBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")
    compile (SCond _ exp stmt) = do
        (llvmCode, val) <- compileExpr exp
        thenBlock <- compile stmt
        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN
        return $ llvmCode <> singleton ("br i1 " ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ endLabel ++ "\n") <>
            singleton (tail condTrueLabel ++ ":\n") <> thenBlock <> singleton ("br label " ++ endLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")
    compile (SAss _ lval exp) = do
        (llvmCodeLVal, valLVal) <- compileLVal lval
        (llvmCodeExp, valExp) <- compileExpr exp
        let valExpType = llvmType valExp
        return $ llvmCodeLVal <> llvmCodeExp <> singleton ("store " ++ show valExpType ++ " " ++ show valExp ++ ", " ++ show (PointerType valExpType) ++ " " ++ show valLVal ++ "\n")
    compile (SWhile _ exp stmt) = do
        (llvmCode, val) <- compileExpr exp
        loopLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabelN + 1 })
        let condLabel = "%loopCond" ++ show loopLabelN
        let loopLabel = "%loop" ++ show loopLabelN
        let endLabel = "%loopEnd" ++ show loopLabelN
        body <- compile stmt
        return $ singleton ("br label " ++ condLabel ++ "\n") <>
            singleton (tail condLabel ++ ":\n") <> llvmCode <> singleton ("br i1 " ++ show val ++ ", label " ++ loopLabel ++ ", label " ++ endLabel ++ "\n") <>
            singleton (tail loopLabel ++ ":\n") <>
            body <> singleton ("br label " ++ condLabel ++ "\n") <>
            singleton (tail endLabel ++ ":\n")

getRawString :: Value -> IM (Data.Sequence.Seq String, Value)
getRawString (StringLiteral ind length) = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (PointerType I8Type)
    return (
        singleton (show returnReg ++ " = getelementptr inbounds [" ++ show length ++ " x i8], [" ++ show length ++ " x i8]* @strings" ++ show ind ++ ", i32 0, i32 0\n"),
        returnReg
        )
getRawString reg@(Register loc (PointerType I8Type)) = return (
    singleton "",
    reg
    )

concatStrings :: Expr -> Expr -> IM (Data.Sequence.Seq String, Value)
concatStrings expr1 expr2 = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    (loadCode1, val1') <- getRawString val1
    (loadCode2, val2') <- getRawString val2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (PointerType I8Type)
    return (
        llvmCode1 <> llvmCode2 <> loadCode1 <> loadCode2 <>
        singleton (show returnReg ++ " = call i8* @__internal_concat(i8* " ++ show val1' ++ ", i8* " ++ show val2' ++ ")\n"),
        returnReg
        )


getMethodType2 :: Ident -> Ident -> Map Ident Class -> Maybe PrimitiveType
getMethodType2 className methodName classMap = 
    Data.Map.lookup className classMap >>= \(Class _ _ methods) -> Data.List.lookup methodName methods

-- Function to retrieve method index in the vtable
getMethodIndex2 :: Ident -> Ident -> Map Ident Class -> Maybe Int
getMethodIndex2 className methodName classMap = 
    Data.Map.lookup className classMap >>= \(Class _ _ methods) -> 
        let methodNames = map fst methods
        in Data.List.elemIndex methodName methodNames

-- getFunctionIdent :: Maybe Ident -> Ident -> Ident
-- getFunctionIdent Nothing (Ident name) = "@" ++ name

compileExpr :: Expr -> IM (Data.Sequence.Seq String, Value)
compileExpr (EMethodApply _ expr method args) = do
    (llvmCode, val) <- compileExpr expr
    compiledArgs <- traverse compileExpr args
    let llvmCodeArgs = mconcat . map fst $ compiledArgs
    let argVals = map snd compiledArgs
    let argTypes = map llvmType argVals
    let argsStr = Data.List.intercalate ", " $ zipWith (\ argType argVal -> show argType ++ " " ++ show argVal) argTypes argVals

    let clsname = case val of
            Register _ (PointerType (ClassType clsName)) -> clsName
            _ -> error "Internal compiler error: trying to call method on non-class"
    
    -- first entry of an object is pointer to vtable
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let vtablePtrReg = Register loc (PointerType (ClassVtableType clsname))
    classes' <- classes <$> ask
    let methodType' = getMethodType2 clsname method classes'
    let methodType = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodType'
    let methodIndex' = getMethodIndex2 clsname method classes'
    let methodIndex = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodIndex'
    let codeGetVtablePtr = singleton (show vtablePtrReg ++ " = getelementptr " ++ show (ClassType clsname) ++ ", " ++ show (PointerType (ClassType clsname)) ++ " " ++ show val ++ ", i32 0, i32 0\n")
    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let vtableReg = Register loc2 (ClassVtableType clsname)
    let codeLoadVtable = singleton (show vtableReg ++ " = load " ++ show (PointerType (ClassVtableType clsname)) ++ ", " ++ show (PointerType (PointerType (ClassVtableType clsname))) ++ " " ++ show vtablePtrReg ++ "\n")
    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let methodPtrReg = Register loc3 (PointerType methodType)
    let getMethodPtr = singleton (show methodPtrReg ++ " = getelementptr " ++ show (ClassVtableType clsname) ++ ", " ++ show (PointerType (ClassVtableType clsname)) ++ " " ++ show vtableReg ++ ", i32 0, i32 " ++ show methodIndex ++ "\n")
    loc4 <- gets currentLoc
    modify (\st -> st { currentLoc = loc4 + 1 })
    let methodReg = Register loc4 methodType
    let loadMethod = singleton (show methodReg ++ " = load " ++ show (PointerType methodType) ++ ", " ++ show (PointerType (PointerType methodType)) ++ " " ++ show methodPtrReg ++ "\n")
    loc5 <- gets currentLoc
    modify (\st -> st { currentLoc = loc5 + 1 })
    let returnRegister = Register loc (PointerType I8Type)
    env <- ask
    let methodReturnType = case methodType of
            FunctionType retType _ -> retType
            _ -> error "Internal compiler error: method type is not a function"
    let evalMethod = singleton (show returnRegister ++ " = call " ++ show (PointerType I8Type) ++ " " ++ show methodReg ++ "(" ++ show (PointerType (ClassType clsname)) ++ " " ++ show val ++ ", i8* " ++ show vtablePtrReg ++ ", " ++ argsStr ++ ")\n")
    return (llvmCode <> llvmCodeArgs <> codeGetVtablePtr <> codeLoadVtable <> getMethodPtr <> loadMethod <> evalMethod, returnRegister)

compileExpr (EApp _ (Ident ident) args) = do
    compiledArgs <- traverse compileExpr args
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
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    let argType = llvmType val1
    let llvmCode = llvmCode1 <> llvmCode2
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
    (llvmCode1, val1) <- compileExpr expr1
    case val1 of
        StringLiteral ind length -> concatStrings expr1 expr2
        Register loc (PointerType I8Type) -> concatStrings expr1 expr2
        _ -> do
            (llvmCode2, val2) <- compileExpr expr2
            let argType = llvmType val1

            let llvmCode = llvmCode1 <> llvmCode2
            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let returnReg = Register loc argType
            case op of
                OpAdd _ -> return (llvmCode <> singleton (show returnReg ++ " = add " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EAdd\n"), returnReg)
                OpSub _ -> return (llvmCode <> singleton (show returnReg ++ " = sub " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; ESub\n"), returnReg)
compileExpr (EMul _ expr1 op expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    let argType = llvmType val1
    let llvmCode = llvmCode1 <> llvmCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc argType
    case op of
        OpMul _ -> return (llvmCode <> singleton (show returnReg ++ " = mul " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EMul\n"), returnReg)
        OpDiv _ -> return (llvmCode <> singleton (show returnReg ++ " = sdiv " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EDiv\n"), returnReg)
        OpMod _ -> return (llvmCode <> singleton (show returnReg ++ " = srem " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "; EMod\n"), returnReg)

compileExpr (ELitNull _) = error $ "Not implemented: nulls "
compileExpr (ELitInt _ int) = pure (singleton "", ConstValue (I32 int))
compileExpr (EString _ str) = do
    ind <- addNewString str
    return (singleton "\n", StringLiteral ind (toInteger $ length str + 1))
compileExpr (ELitTrue _) = pure (singleton "", ConstValue (I1 True))
compileExpr (ELitFalse _) = pure (singleton "", ConstValue (I1 False))
compileExpr (ENot _ expr) = do
    (llvmCode, val) <- compileExpr expr
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc I1Type
    return (llvmCode <> singleton (show returnReg ++ " = xor i1 1, " ++ show val ++ "\n"), returnReg)
compileExpr (EOr _ expr1 _ expr2) = do
    (code, val) <- compileExpr (ENot BNFC'NoPosition (EAnd BNFC'NoPosition (ENot BNFC'NoPosition expr1) (OpAnd BNFC'NoPosition) (ENot BNFC'NoPosition expr2)))
    return (code, val)
compileExpr (EAnd _ expr1 _ expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    labelAnd <- gets currentLabel
    modify (\st -> st { currentLabel = labelAnd + 1 })
    (llvmCode2, val2) <- compileExpr expr2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    resultLoc <- gets currentLoc
    modify (\st -> st { currentLoc = resultLoc + 1 })
    let labelStart = "%andStart" ++ show labelAnd
    let labelCheckSecond = "%andCheckSecond" ++ show labelAnd
    let labelCheckSecondEnd = "%andCheckSecondEnd" ++ show labelAnd
    let labelEnd = "%andEnd" ++ show labelAnd
    let returnReg = Register resultLoc I1Type
    return (
        llvmCode1 <>
        singleton ("br label " ++ labelStart ++ "\n") <>
        singleton (tail labelStart ++ ":\n") <>
        singleton ("br i1 " ++ show val1 ++ ", label " ++ labelCheckSecond ++ ", label " ++ labelEnd ++ "\n") <>
        singleton (tail labelCheckSecond ++ ":\n") <>
        llvmCode2 <>
        singleton ("br label " ++ labelCheckSecondEnd ++ "\n") <>
        singleton (tail labelCheckSecondEnd ++ ":\n") <>
        singleton ("br label " ++ labelEnd ++ "\n") <>
        singleton (tail labelEnd ++ ":\n") <>
        singleton (show returnReg ++ " = phi i1 [ false, " ++ labelStart ++ " ], [ " ++ show val2 ++ ", " ++ labelCheckSecondEnd ++ " ]\n")
        , returnReg)

compileExpr (ENewArr _ type_ expr) = pure (singleton "", Register 0 (PointerType I8Type))
compileExpr (ENew _ ident) = do
    -- construct a default object of class ident
    classes' <- classes <$> ask
    let class_ = case Data.Map.lookup ident classes' of
            Just cls -> cls
            Nothing -> error $ "Internal compiler error: class " ++ show ident ++ " not found"
    -- use malloc to allocate memory for the object
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let callocReg = Register loc (PointerType I8Type)
    let callocCode = singleton (show callocReg ++ " = call i8*  @__calloc(i32 " ++ show (classSize class_) ++ ")\n")
    -- bitcast
    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let bitcastReg = Register loc2 (PointerType (ClassType ident))
    let bitcastCode = singleton (show bitcastReg ++ " = bitcast i8* " ++ show callocReg ++ " to " ++ show (PointerType (ClassType ident)) ++ "\n")
    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let vtableReg = Register loc3 (PointerType (ClassVtableType ident))
    let vtableFetchCode = singleton (show vtableReg ++ " = getelementptr inbounds " ++ show (ClassType ident) ++ ", " ++ show (PointerType (ClassType ident)) ++ " " ++ show bitcastReg ++ ", i32 0, i32 0\n")
    -- store vtable in allocated object
    storeCode <- storeVtable ident vtableReg
    return (callocCode <> bitcastCode <> vtableFetchCode <> storeCode, bitcastReg)


storeVtable :: Ident -> Value -> IM (Data.Sequence.Seq String)
storeVtable ident@(Ident i) objReg = do
    let vtable = "@vtable." ++ i
    return $ singleton ("store " ++ show (PointerType (ClassVtableType ident)) ++ " " ++ vtable ++ ", " ++ show (PointerType (PointerType (ClassVtableType ident))) ++ " " ++ show objReg ++ "\n")

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
compileLVal (LArrAcc _ expr1 expr2) = pure (singleton "", Register 0 (PointerType I8Type))
compileLVal (LAttrAcc _ expr (Ident ident)) = pure (singleton "", Register 0 (PointerType I8Type))
