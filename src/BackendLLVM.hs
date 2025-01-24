{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module BackendLLVM ( emitLLVM ) where

import Latte.Abs
import Control.Monad.Except ( throwError, runExceptT, ExceptT, runExcept )

import Control.Monad.RWS (RWST (runRWST), tell)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader (local), ask, asks)
import Control.Monad.Identity (Identity (runIdentity))
import Data.Map (Map, empty, fromList, lookup, union, size, insert)
import qualified Data.Map
import Data.Sequence (singleton, Seq, intersperse, empty)
import Control.Monad.State (State, StateT (runStateT), runState, gets, modify, put, get)
import Control.Monad.Writer (WriterT (runWriterT))
import qualified Data.Foldable
import qualified Control.Monad.RWS as Data.Sequence
import qualified Data.List
import Data.Maybe (Maybe, fromMaybe, maybeToList)
import Data.Foldable (toList, traverse_)
import Data.Char(ord)
import Numeric(showHex)
import Text.ParserCombinators.ReadP (char, option)
import Data.Graph (Graph, Vertex, graphFromEdges, topSort)
import Control.Monad (zipWithM)


-- functions to create the strings pool
charToHex :: Char -> String
charToHex c = do
    let hex = showHex (ord c) ""
    if length hex == 1 then "\\0" ++ hex else "\\" ++ hex

addNewString :: String -> IM Integer
addNewString str = do
    strings <- gets strings
    case Data.Map.lookup str strings of
        Just ind -> return ind
        Nothing -> do
            let ind = toInteger $ Data.Map.size strings
            modify (\st -> st { strings = Data.Map.insert str ind strings })
            return ind


newtype Label = Label String

instance Show Label where
    show (Label l) = l

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
    | ArrType PrimitiveType
    deriving (Eq)

data Primitive =
    I1 Bool
    | I8 Integer
    | I32 Integer
    | Nullptr
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
    show (Pointer p) = show p ++ "*"
    show Nullptr = "null"

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
    llvmType Nullptr = PointerType I8Type


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
    llvmType (TArr _ type_) = PointerType $ ArrType $ llvmType type_

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
    show (ArrType type_) = "%Array"

data St = St {
    strings :: Map String Integer,
    currentLoc :: Integer,
    currentLabel :: Integer,
    currentBlock :: BasicBlock,
    localVars :: Map Ident Value
}
initState :: St
initState = St {
    strings = Data.Map.empty,
    currentLoc = 0,
    currentBlock = BasicBlock Nothing [] [],
    localVars = Data.Map.empty,
    currentLabel = 0
}

data Class = Class {
    parent :: Maybe Ident,
    fields :: [(Ident, PrimitiveType)],
    -- (Ident tell, "@Shape_tell", i32(Shape *)*)
    methods :: [(Ident, String, PrimitiveType)]
} deriving (Show)

getMethodType :: Ident -> ClsMemDeclC -> [(Ident, PrimitiveType)]
getMethodType cls@(Ident iden) (ClsMthdDecl _ mt@(FunDef _ retType (Ident funiden) args _)) = do
    [(Ident funiden, llvmType mt)]
getMethodType _ (ClsAttrDecl {}) = []

getMethodTypes :: ClsDefC -> [(Ident, PrimitiveType)]
getMethodTypes (ClsDef _ ident mems) = concatMap (getMethodType ident) mems
getMethodTypes (ClsDefExt _ ident _ mems) = concatMap (getMethodType ident) mems

getClassName :: ClsDefC -> Ident
getClassName (ClsDef _ ident _) = ident
getClassName (ClsDefExt _ ident _ _) = ident

getParentName :: ClsDefC -> Maybe Ident
getParentName (ClsDef {}) = Nothing
getParentName (ClsDefExt _ _ ident _) = Just ident

getMethodIdent :: Ident -> Ident -> Ident
getMethodIdent (Ident cls) (Ident method) = Ident $ "@" ++ cls ++ "_" ++ method

processClass :: Map Ident Class -> ClsDefC -> Map Ident Class
processClass acc cls =
    let inheritedFields  = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . fields)) (getParentName cls)
        inheritedMethods = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . methods)) (getParentName cls)
        ownMethods = getMethodTypes cls
        methods' = f inheritedMethods ownMethods
        newClass = Class (getParentName cls) (inheritedFields ++ getAttrTypes cls) methods'
    in Data.Map.insert (getClassName cls) newClass acc
    where
        methodName (name, _) = name
        methodAddStem (Ident name, t) = (Ident name, "@" ++ getClassNameStr cls ++ "_" ++ name, t)
        getClassNameStr (ClsDef _ (Ident name) _) = name
        getClassNameStr (ClsDefExt _ (Ident name) _ _) = name

        f :: [(Ident, String, PrimitiveType)] -> [(Ident, PrimitiveType)] -> [(Ident, String, PrimitiveType)]
        f inheritedMethods ownMethods = do
            -- if an inherited method is later overriden, we need to replace it
            let inheritedReplacedByVirtual = map (\(name, s, t) -> case Data.List.find (\(name2, _) -> name == name2) ownMethods of
                    Just (_, t2) -> methodAddStem (name, t2)
                    Nothing -> (name, s, t)
                    ) inheritedMethods
            -- if own method was inherited, we need t remove it
            let ownFiltered = filter (\(name, _) -> name `notElem` map fst3 inheritedMethods) ownMethods
            inheritedReplacedByVirtual ++ map methodAddStem ownFiltered
        
        fst3 (a, _, _) = a


createClassMap :: [ClsDefC] -> Map Ident Class
createClassMap clsDefs =
    let (graph, nodeFromVertex, _) = graphFromEdges [(cls, getClassName cls, findChildren clsDefs cls) | cls <- clsDefs]
        findChildren :: [ClsDefC] -> ClsDefC -> [Ident]
        findChildren defs parentCls = [getClassName cls | cls <- defs, getParentName cls == Just (getClassName parentCls)]
        sortedVertices = topSort graph
        sortedClasses = map (\tv -> let (cls, _, _) = nodeFromVertex tv in cls) sortedVertices
    in foldl processClass Data.Map.empty sortedClasses

classSize :: Class -> Integer
classSize cls = do
    let fields' = fields cls
    8 + 8 * toInteger (length fields')

getMethodType2 :: Ident -> Ident -> Map Ident Class -> Maybe PrimitiveType
getMethodType2 className methodName classMap =
    Data.Map.lookup className classMap >>= \(Class _ _ methods) -> lookup3 methodName methods
    where
        lookup3 :: Ident -> [(Ident, String, PrimitiveType)] -> Maybe PrimitiveType
        lookup3 methodName methods = do
            let methodNames = map (\(name, _, _) -> name) methods
            let methodTypes = map (\(_, _, type_) -> type_) methods
            ind <- Data.List.elemIndex methodName methodNames
            return $ methodTypes !! ind

getMethodType22 :: Ident -> Ident -> Map Ident Class -> Maybe (PrimitiveType, String)
getMethodType22 className methodName classMap =
    Data.Map.lookup className classMap >>= \(Class _ _ methods) -> lookup3 methodName methods
    where
        lookup3 methodName methods = do
            let methodNames = map (\(name, _, _) -> name) methods
            let methodTypes = map (\(_, name, type_) -> (type_, name)) methods
            ind <- Data.List.elemIndex methodName methodNames
            return $ methodTypes !! ind


-- Function to retrieve method index in the vtable
getMethodIndex :: Ident -> Ident -> Map Ident Class -> Maybe Int
getMethodIndex className methodName classMap =
    Data.Map.lookup className classMap >>= \(Class _ _ methods) ->
        let methodNames = map fst3 methods
        in Data.List.elemIndex methodName methodNames
    where
        fst3 (a, _, _) = a

getAttrIndex :: Ident -> Ident -> Map Ident Class -> Maybe Int
getAttrIndex className attrName classMap =
    Data.Map.lookup className classMap >>= \(Class _ fields _) -> do
        let fieldNames = map fst fields
        -- vtable pointer is at 0
        ind <- Data.List.elemIndex attrName fieldNames
        return $ ind + 1

getAttrType3 :: Ident -> Ident -> Map Ident Class -> Maybe PrimitiveType
getAttrType3 className attrName classMap =
    Data.Map.lookup className classMap >>= \(Class _ fields _) ->
        Data.List.lookup attrName fields

-- getFunctionIdent :: Maybe Ident -> Ident -> Ident
-- getFunctionIdent Nothing (Ident name) = "@" ++ name


getAttrType :: ClsMemDeclC -> [(Ident, PrimitiveType)]
getAttrType (ClsMthdDecl _ _) = []
getAttrType (ClsAttrDecl _ t items) = map (\(AttrItem _ ident) -> (ident, llvmType t)) items

getAttrTypes :: ClsDefC -> [(Ident, PrimitiveType)]
getAttrTypes (ClsDef _ _ mems) = concatMap getAttrType mems
getAttrTypes (ClsDefExt _ _ _ mems) = concatMap getAttrType mems

addSelfArgument :: Ident -> FunDefC -> FunDefC
addSelfArgument (Ident clsName) (FunDef pos retType ident args block) = FunDef pos retType ident (Arg pos (TCls pos (Ident clsName)) (Ident "self") : args) block

addSelfArgumentsClsMem :: Ident -> ClsMemDeclC -> ClsMemDeclC
addSelfArgumentsClsMem clsName (ClsMthdDecl pos funDef) = ClsMthdDecl pos (addSelfArgument clsName funDef)
addSelfArgumentsClsMem _ clsAttrDecl = clsAttrDecl

addSelfArgumentsCls :: ClsDefC -> ClsDefC
addSelfArgumentsCls (ClsDef pos ident mems) = ClsDef pos ident (map (addSelfArgumentsClsMem ident) mems)
addSelfArgumentsCls (ClsDefExt pos ident parent mems) = ClsDefExt pos ident parent (map (addSelfArgumentsClsMem ident) mems)

addSelfArguments :: [TopDefC] -> [TopDefC]
addSelfArguments [] = []
addSelfArguments (f@(FunDefTop pos funDef) : rest) = f : addSelfArguments rest
addSelfArguments (ClsDefTop pos clsDef : rest) = ClsDefTop pos (addSelfArgumentsCls clsDef) : addSelfArguments rest

createVtable :: Ident -> IM String
createVtable (Ident clsName) = do
    classes' <- asks classes
    let cls = Data.Map.lookup (Ident clsName) classes'
    case cls of
        Nothing -> error "Internal compiler error: class not found"
        Just (Class parent fields methods) -> do
            let vtableType = "%vtable." ++ clsName ++ ".type = type { " ++ Data.List.intercalate ", " (map (\(_, _, type_) -> show type_) methods) ++ "} ; with inherited :) \n"
            let vtable = "@vtable." ++ clsName ++ " = global %vtable." ++ clsName ++ ".type { " ++ Data.List.intercalate ", " (map f methods) ++ " }\n"
            let structName = "%class." ++ clsName
            let vtable_ptr = ["%vtable." ++ clsName ++ ".type*"]
            let members = map (\(Ident name, type_) -> (name, type_)) fields
            let structDecl = unlines [
                    structName ++ " = type { ",
                    Data.List.intercalate ", " (vtable_ptr ++ map (\(_, type_) -> show type_) members),
                    "}"
                    ]
            return $ vtableType ++ vtable ++ structDecl ++ "\n"
    where
        f (_, s, type_) = show type_ ++ " " ++ s

-- doesn't have to be a basic block per se,
-- e.g. class definition will also be stored in this data structure
-- if not a basic block, label is empty
data BasicBlock = BasicBlock {
    label :: Maybe Label,
    instructions :: [Instruction],
    predecessors :: [Label]
}

data Env = Env {
    var :: Map Ident Value,
    functions :: Map Ident (PrimitiveType, [PrimitiveType]),
    classes :: Map Ident Class,
    returnType :: Maybe PrimitiveType,
    currentClass :: Maybe Ident
}
initEnv :: Env
initEnv = Env {
    var = Data.Map.empty,
    returnType = Nothing,
    functions = Data.Map.fromList [
        (Ident "printInt", (VoidType, [I32Type])),
        (Ident "printString", (VoidType, [PointerType I8Type])),
        (Ident "error", (VoidType, [])),
        (Ident "readInt", (I32Type, [])),
        (Ident "readString", (PointerType I8Type, []))
        ],
    classes = Data.Map.empty,
    currentClass = Nothing
}

type IM = ReaderT Env (State St)
runIM :: IM a -> Env -> St -> (a, St)
runIM k env = runState (runReaderT k env)

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

createFunctionEnv :: [FunDefC] -> Map Ident (PrimitiveType, [PrimitiveType])
createFunctionEnv funs = Data.Map.fromList $ map (\(FunDef _ retType name args _) -> (name, (llvmType retType, map (\(Arg _ type_ _) -> llvmType type_) args))) funs

emitLLVM :: ProgramC -> String
emitLLVM prog@(Program _ topDefs) = do
    let funs = filterFuns topDefs
    let initFunctionEnv = Data.Map.union (createFunctionEnv funs) (functions initEnv)
    let (blocks, _) = runIM (compile prog) (initEnv {functions = initFunctionEnv}) initState
    let initCode = unlines [
            "declare void @printInt(i32)",
            "declare void @printString(i8*)",
            "declare void @error()",
            "declare i32 @readInt()",
            "declare i8* @readString()",
            "declare i8* @__internal_concat(i8*, i8*)",
            "declare i8* @__calloc(i32)",
            "declare i1 @__internal_strcmp(i8*, i8*)",
            "%Array = type { i32, i8* }"
            ]
    initCode ++ concatMap show blocks

instance Show BasicBlock where
    show (BasicBlock label instructions predecessors) = do
        let predecessorsStr = concatMap (\(Label l) -> "  %" ++ show l) predecessors ++ "\n"
        let instructionsStr = concatMap show instructions ++ "\n"
        case label of
            Nothing -> instructionsStr
            (Just (Label "invalid")) -> ""
            (Just l) -> show l ++ ": ;" ++ predecessorsStr ++ instructionsStr

class Compilable a where
    compile :: a -> IM [BasicBlock]

instance Compilable ProgramC where
    compile (Program _ topDefs') = do
        let topDefs = addSelfArguments topDefs'
        env' <- ask
        let env = env' { classes = createClassMap (filterCls topDefs) }
        compiledTopDefs <- traverse (local (const env) . compile) topDefs
        let code = mconcat compiledTopDefs

        _ <- addNewString ""
        allStrings <- gets strings
        let prepString rawStr = "\"" ++ concatMap charToHex rawStr ++ "\\00\""
        let llvmStrings = unlines $ map (\(str, ind) -> "@strings" ++ show ind ++ " = private constant [" ++ show (length str + 1) ++ " x i8] c" ++ prepString str ++ "\n") $ Data.Map.toList allStrings
        vtables <- local (const env) (getVtables $ filterCls topDefs)
        let basicBlock = BasicBlock Nothing [Custom llvmStrings, Custom vtables] []
        return $ basicBlock : code

instance Compilable TopDefC where
    compile (FunDefTop _ def) = compile def
    compile (ClsDefTop _ def) = compile def

getVtables :: [ClsDefC] -> IM String
getVtables clsDefs = do
    vtables <- traverse (createVtable . getClassName) clsDefs
    return $ unlines vtables

instance Compilable ClsDefC where
    compile c@(ClsDef _ i@(Ident nam) mems) = do
        env <- ask
        results <- traverse (local (const env {currentClass = Just i}) . compile) mems
        return $ mconcat results
    compile (ClsDefExt p i _ mems) = compile (ClsDef p i mems)

makeMethodName :: Ident -> Ident -> String
makeMethodName (Ident cls) (Ident method) = cls ++ "_" ++ method

instance Compilable ClsMemDeclC where
    compile (ClsMthdDecl _ (FunDef p r i a b)) = do
        cls <- asks currentClass
        case cls of
            Nothing -> error "Internal compiler error: no current class"
            Just cls -> do
                let funDef = FunDef p r (Ident $ makeMethodName cls i) a b
                compile funDef
    compile (ClsAttrDecl _ _ items) = pure []

getLabelOfCurrentBlock :: IM Label
getLabelOfCurrentBlock = do
    block <- gets currentBlock
    case label block of
        Nothing -> error "Internal compiler error: no label"
        Just l -> return l

instance Compilable FunDefC where
    compile (FunDef _ retType_ (Ident name) args block@(Block _ stmts)) = do
        let retType = llvmType retType_
        let argsStr = Data.List.intercalate ", " $ map (\(Arg _ type_ (Ident i)) -> show (llvmType type_) ++ " %" ++ i) args
        let header = Custom $ unlines [
                "define " ++ show retType ++ " @" ++ name ++ "(" ++ argsStr ++ ") {"
                ]
        initLoc <- gets currentLoc
        varLocs <- traverse (\(Arg _ type_ (Ident name)) -> do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                return (Ident name, Register loc (PointerType $ llvmType type_))
                ) args
        let newVars = Data.Map.fromList varLocs
        modify (\st -> st { currentLoc = initLoc })

        let headerBlock = BasicBlock Nothing [header] []

        lab <- gets currentLabel
        modify (\st -> st { currentLabel = lab + 1 })
        let openingLabel = Label $ "entry" ++ show lab

        let openingBlock = BasicBlock (Just openingLabel) [] []
        modify (\st -> st { currentBlock = openingBlock })

        traverse_ (\(Arg _ type_ (Ident name)) -> do
                let llvmTypeArg = llvmType type_
                let llvmTypeReg = PointerType llvmTypeArg
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let register = Register loc llvmTypeReg
                addToCurrentBlock (Alloca register)
                addToCurrentBlock (Custom $ "store " ++ show llvmTypeArg ++ " %" ++ name ++ ", " ++ show llvmTypeReg ++ " " ++ show register ++ " ; already loaded\n")
                ) args

        let retStmt = case retType of
                VoidType -> SRetVoid BNFC'NoPosition
                I32Type -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                I1Type -> SRetExp BNFC'NoPosition (ELitFalse BNFC'NoPosition)
                PointerType (ClassType _) -> SRetExp BNFC'NoPosition (ECast BNFC'NoPosition retType_ (TokNull ""))
                PointerType _ -> SRetExp BNFC'NoPosition (ELitInt BNFC'NoPosition 0)
                _ -> error "Internal compiler error: no return type"
        let block' = Block BNFC'NoPosition (stmts ++ [retStmt])
        basicblocks <- local (\env -> env { returnType = Just retType, var = newVars }) $ do
            compile block'

        -- addToCurrentBlock defaultRet
        let endBlock = BasicBlock Nothing [Custom "}"] []
        -- endblock <- gets currentBlock
        -- modify (\st -> st { currentBlock = BasicBlock (Just $ Label "invalid") [] [] })

        return $ (headerBlock  : basicblocks) ++ [endBlock]
        -- return $ (prevBlock : headerBlock  : basicblocks) ++ [endblock]


instance Compilable BlockC where
    compile (Block _ []) = pure []
    compile (Block _ stmts) = do
        prev_vars <- gets localVars
        compiledStmts <- traverse compile stmts
        modify (\st -> st { localVars = prev_vars })
        return $ mconcat compiledStmts

addToCurrentBlock :: Instruction -> IM ()
addToCurrentBlock ins = do
    block <- gets currentBlock
    modify (\st -> st { currentBlock = block { instructions = instructions block ++ [ins] } })

getNewRegister :: PrimitiveType -> IM Value
getNewRegister type_ = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    return $ Register loc type_

dereference :: Value -> IM ([BasicBlock], Value)
dereference val = case val of
    reg@(Register loc (PointerType p)) -> do
        returnReg <- getNewRegister p
        addToCurrentBlock (Load returnReg reg)
        return ([], returnReg)
    _ -> error $ "Internal compiler error: trying to dereference non-pointer: " ++ show (llvmType val)

dereferenceType :: Value -> PrimitiveType
dereferenceType (Register _ (PointerType p)) = p
dereferenceType _ = error "Internal compiler error: trying to dereference non-pointer type!"

compileBinOp :: PrimitiveType -> Value -> Value -> String -> IM ([BasicBlock], Value)
compileBinOp type_ val1 val2 op = do
    returnReg <- getNewRegister type_
    let ins = Custom (show returnReg ++ " = " ++ op ++ " " ++ show type_ ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n")
    addToCurrentBlock ins
    return ([], returnReg)

data Instruction =
    Store Value Value
    | Load Value Value
    | RetVoid
    | Ret Value
    | Alloca Value
    | Custom String

instance Show Instruction where
    show (Load returnReg addr) = show returnReg ++ " = load " ++ show (dereferenceType addr) ++ ", " ++ show (llvmType addr) ++ " " ++ show addr ++ "\n"
    show (Store val1 val2) = "store " ++ show (llvmType val1) ++ " " ++ show val1 ++ ", " ++ show (llvmType val2) ++ " " ++ show val2 ++ "\n"
    show RetVoid = "ret void\n"
    show (Ret val) = "ret " ++ show (llvmType val) ++ " " ++ show val ++ "\n"
    show (Alloca val) = case llvmType val of
        PointerType type_ -> show val ++ " = alloca " ++ show type_ ++ "\n"
        _ -> error "Internal compiler error: alloca returns a non-pointer"
    show (Custom str) = str ++ "\n"

-- optionallyBitcast (neededtype, val)
optionallyBitcast :: PrimitiveType -> Value -> IM Value
optionallyBitcast (PointerType (ClassType (Ident neededClass))) val = do
    case llvmType val of
        PointerType (ClassType (Ident name2)) -> do
            if neededClass /= name2 then do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let returnReg = Register loc (PointerType $ ClassType (Ident neededClass))
                let ins = Custom (show returnReg ++ " = bitcast " ++ show (PointerType $ ClassType (Ident name2)) ++ " " ++ show val ++ " to " ++ show (PointerType $ ClassType (Ident neededClass)) ++ "\n")
                addToCurrentBlock ins
                return returnReg
            else do
                addToCurrentBlock (Custom "; no bitcast needed because classes match")
                return val
        PointerType _ -> do
            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let returnReg = Register loc (PointerType $ ClassType (Ident neededClass))
            let ins = Custom (show returnReg ++ " = bitcast " ++ show (llvmType val) ++ " " ++ show val ++ " to " ++ show (PointerType $ ClassType (Ident neededClass)) ++ "\n")
            addToCurrentBlock ins
            return returnReg
        _ -> do
            addToCurrentBlock (Custom "; no bitcast needed because not a class pointer")
            return val
optionallyBitcast (PointerType (ArrType t)) val = do
    case llvmType val of
        PointerType (ArrType _) -> do
            addToCurrentBlock (Custom "; no bitcast needed because both are arrays")
            return val
        _ -> do
            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let returnReg = Register loc (PointerType $ ArrType t)
            let ins = Custom (show returnReg ++ " = bitcast " ++ show (llvmType val) ++ " " ++ show val ++ " to " ++ show (llvmType returnReg) ++ "\n")
            addToCurrentBlock ins
            return returnReg
optionallyBitcast p val = do
    addToCurrentBlock (Custom ("; no bitcast because no class pointer needed: " ++ show p))
    return val


instance Compilable Stmt where
    compile (SEmpty _) = pure []
    compile (SBlock _ block) = compile block
    compile (SExp _ expr) = fst <$> compileExpr expr
    compile (SIncr _ lval) = do
        (llvmCode, val) <- compileLVal lval
        (loadCode, valLoaded) <- dereference val
        (incrCode, incrVal) <- compileBinOp (llvmType valLoaded) valLoaded (ConstValue (I32 1)) "add"
        let storeIns = Store incrVal val
        addToCurrentBlock storeIns
        return $ llvmCode ++ loadCode ++ incrCode
    compile (SDecr _ lval) = do
        (llvmCode, val) <- compileLVal lval
        (loadCode, valLoaded) <- dereference val
        (decrCode, decrVal) <- compileBinOp (llvmType valLoaded) valLoaded (ConstValue (I32 1)) "sub"
        let storeIns = Store decrVal val
        addToCurrentBlock storeIns
        return $ llvmCode ++ loadCode ++ decrCode
    compile (SRetVoid _) = do
        addToCurrentBlock RetVoid
        block <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label "invalid")[] [] })
        return [block]
    compile (SRetExp _ exp) = do
        (llvmCode, val) <- compileExpr exp
        env <- ask
        let retType = fromMaybe (error "Internal compiler error: no return type") (returnType env)
        casted <- optionallyBitcast retType val
        addToCurrentBlock (Ret casted)
        block <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label "invalid") [] [] })
        return $ llvmCode ++ [block]
    compile (SDecl _ decltype items) = do
        initExprs <- traverse declareItem items
        return $ mconcat initExprs
        where
            declareItem :: DeclItem' BNFC'Position -> IM [BasicBlock]
            declareItem (DeclInit _ ident expr) = do
                (llvmCode, val) <- compileExpr expr
                reg <- getNewRegister (PointerType $ llvmType decltype)
                modify (\st -> st { localVars = Data.Map.insert ident reg (localVars st) })
                addToCurrentBlock (Alloca reg)
                casted <- optionallyBitcast (llvmType decltype) val
                addToCurrentBlock (Store casted reg)
                addToCurrentBlock (Custom ("; SDecl ;)" ++ show (llvmType decltype)  ++ " " ++ show (llvmType val)))
                return llvmCode
            declareItem (DeclNoInit _ ident) = do
                reg <- getNewRegister (PointerType $ llvmType decltype)
                modify (\st -> st { localVars = Data.Map.insert ident reg (localVars st) })
                addToCurrentBlock (Alloca reg)
                -- default initialize
                case decltype of
                    TStr _ -> do
                        emptyStringInd <- addNewString ""
                        loc <- gets currentLoc
                        modify (\st -> st { currentLoc = loc + 1 })
                        let reg2 = Register loc (PointerType I8Type)
                        addToCurrentBlock (Custom $ show reg2 ++ " = getelementptr [1 x i8], [1 x i8]* @strings" ++ show emptyStringInd ++ ", i32 0, i32 0\n")
                        addToCurrentBlock (Store reg2 reg)
                    TInt _ -> do
                        addToCurrentBlock (Store (ConstValue (I32 0)) reg)
                    TBool _ -> do
                        addToCurrentBlock (Store (ConstValue (I1 False)) reg)
                    TArr _ _ -> do
                        addToCurrentBlock (Custom $ "store " ++ show (llvmType decltype) ++ " null, " ++ show (PointerType $ llvmType decltype) ++ show reg ++ "\n")
                    TCls _ _ -> do
                        addToCurrentBlock (Custom $ "store " ++ show (llvmType decltype) ++ " null, " ++ show (PointerType $ llvmType decltype) ++ show reg ++ "\n")
                    _ -> do
                        error "Internal compiler error: no default initialization for this type"
                return []

    compile (SCondElse _ exp stmt1 stmt2) = do
        (condBlocks, val) <- compileExpr exp

        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let condFalseLabel = "%condFalse" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN

        addToCurrentBlock (Custom $ "br i1" ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ condFalseLabel ++ "\n")
        condEndBlock <- gets currentBlock
        predecessor <- getLabelOfCurrentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condTrueLabel)  [] [predecessor]})
        prevLocalVars <- gets localVars
        thenBlocks <- compile stmt1
        modify (\st -> st { localVars = prevLocalVars })
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        thenEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condFalseLabel) [] [predecessor]})
        prevLocalVars <- gets localVars
        elseBlocks <- compile stmt2
        modify (\st -> st { localVars = prevLocalVars })
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        elseEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] [Label (tail condTrueLabel), Label (tail condFalseLabel)]})
        return $ condBlocks ++ condEndBlock : thenBlocks ++ thenEndBlock : elseBlocks ++ [elseEndBlock]

    compile (SCond _ exp stmt) = do
        (condBlocks, val) <- compileExpr exp

        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN

        addToCurrentBlock (Custom $ "br i1" ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ endLabel ++ "\n")
        condEndBlock <- gets currentBlock
        predecessor <- getLabelOfCurrentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condTrueLabel) [] [predecessor]})
        prevLocalVars <- gets localVars
        thenBlocks <- compile stmt
        modify (\st -> st { localVars = prevLocalVars })
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        thenEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] [Label (tail condTrueLabel), predecessor]})
        return $ condBlocks ++ condEndBlock : thenBlocks ++ [thenEndBlock]

    compile (SAss _ lval exp) = do
        (llvmCodeLVal, valLVal) <- compileLVal lval
        (llvmCodeExp, valExp') <- compileExpr exp
        -- lval: pointer to pointer to point2
        -- valExp': pointer to point3
        valExp <- optionallyBitcast (dereferenceType valLVal) valExp'
        addToCurrentBlock (Store valExp valLVal)
        addToCurrentBlock (Custom "; SAss ;)")
        return $ llvmCodeLVal ++ llvmCodeExp
    compile (SWhile _ exp stmt) = do
        loopLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabelN + 1 })
        let condLabel = "%loopCond" ++ show loopLabelN
        let loopLabel = "%loop" ++ show loopLabelN
        let endLabel = "%loopEnd" ++ show loopLabelN
        addToCurrentBlock (Custom $ "br label " ++ condLabel ++ "\n")
        prevEndBlock <- gets currentBlock
        predecessor <- getLabelOfCurrentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condLabel) [] [predecessor, Label $ tail loopLabel]})
        (condCode, val) <- compileExpr exp
        addToCurrentBlock (Custom $ "br i1 " ++ show val ++ ", label " ++ loopLabel ++ ", label " ++ endLabel ++ "\n")
        condEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail loopLabel) [] [Label $ tail condLabel]})
        prevLocalVars <- gets localVars
        body <- compile stmt
        modify (\st -> st { localVars = prevLocalVars })
        addToCurrentBlock (Custom $ "br label " ++ condLabel ++ "\n")
        bodyEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] [Label $ tail condLabel]})
        return $ prevEndBlock : condCode ++ condEndBlock : body ++ [bodyEndBlock]

    compile (SFor _ typ ident exp stmt) = do
        (llvmCodeExp, val) <- compileExpr exp
        -- get array length
        loc <- gets currentLoc
        modify (\st -> st { currentLoc = loc + 1 })
        let lengthFieldPtr = Register loc (PointerType I32Type)
        let ins = Custom (show lengthFieldPtr ++ " = getelementptr inbounds %Array, " ++ show (llvmType val) ++ " " ++ show val ++ ", i32 0, i32 0 ; get array length field ptr\n")
        addToCurrentBlock ins
        loc' <- gets currentLoc
        modify (\st -> st { currentLoc = loc' + 1 })
        let lengthReg = Register loc' I32Type
        let ins' = Custom (show lengthReg ++ " = load i32, i32* " ++ show lengthFieldPtr ++ "\n")
        addToCurrentBlock ins'

        -- create variable holding the array element
        loc <- gets currentLoc
        modify (\st -> st { currentLoc = loc + 1 })
        let reg = Register loc (PointerType $ llvmType typ)
        let ins = Custom (show reg ++ " = alloca " ++ show (llvmType typ))
        -- create variable holding the index
        loc' <- gets currentLoc
        modify (\st -> st { currentLoc = loc' + 1 })
        let indexReg = Register loc' $ PointerType I32Type
        let ins' = Custom (show indexReg ++ " = alloca i32")
        addToCurrentBlock ins
        addToCurrentBlock ins'
        addToCurrentBlock (Custom $ "store i32 0, i32* " ++ show indexReg)

        -- make cond block
        loopLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabelN + 1 })
        let condLabel = "%loopCond" ++ show loopLabelN
        let loopLabel = "%loop" ++ show loopLabelN
        let endLabel = "%loopEnd" ++ show loopLabelN
        addToCurrentBlock (Custom $ "br label " ++ condLabel ++ "\n")
        prevEndBlock <- gets currentBlock
        predecessor <- getLabelOfCurrentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condLabel) [] [predecessor, Label $ tail loopLabel]})
        -- check if index < length
        loc'' <- gets currentLoc
        modify (\st -> st { currentLoc = loc'' + 1 })
        let condReg = Register loc'' I1Type
        indexLoadLoc <- gets currentLoc
        modify (\st -> st { currentLoc = indexLoadLoc + 1 })
        let indexReg' = Register indexLoadLoc I32Type
        let ins'' = Load indexReg' indexReg
        addToCurrentBlock ins''
        let ins'' = Custom (show condReg ++ " = icmp slt i32 " ++ show indexReg' ++ ", " ++ show lengthReg)
        addToCurrentBlock ins''
        addToCurrentBlock (Custom $ "br i1 " ++ show condReg ++ ", label " ++ loopLabel ++ ", label " ++ endLabel ++ "\n")
        condEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail loopLabel) [] [Label $ tail condLabel]})
        -- body
        -- load array element
        -- bitcast data pointer from i8* to correct type
        loc14 <- gets currentLoc
        modify (\st -> st { currentLoc = loc14 + 1 })
        let loc15 = Register loc14 (PointerType $ PointerType I8Type)
        let ins14 = Custom (show loc15 ++ " = getelementptr inbounds %Array" ++ ", " ++ show (llvmType val) ++ " " ++ show val ++ ", i32 0, i32 1 ; get data ptr\n")
        addToCurrentBlock ins14

        -- load data pointer
        loc15' <- gets currentLoc
        modify (\st -> st { currentLoc = loc15' + 1 })
        let reg16 = Register loc15' (PointerType I8Type)
        let ins15 = Load reg16 loc15
        addToCurrentBlock ins15

        loc16 <- gets currentLoc
        modify (\st -> st { currentLoc = loc16 + 1 })
        let loc17 = Register loc16 (PointerType $ llvmType typ)
        let ins16 = Custom (show loc17 ++ " = bitcast i8* " ++ show reg16 ++ " to " ++ show (PointerType $ llvmType typ) ++ " ; bitcast data ptr\n")
        addToCurrentBlock ins16

        loc''' <- gets currentLoc
        modify (\st -> st { currentLoc = loc''' + 1 })
        let elementPtr = Register loc''' (PointerType $ llvmType typ)
        let ins''' = Custom (show elementPtr ++ " = getelementptr " ++ show (llvmType typ) ++ ", " ++ show (llvmType loc17) ++ " " ++ show loc17 ++ ", i32 " ++ show indexReg' ++ " ; get array element ptr\n")
        addToCurrentBlock ins'''

        loc'''' <- gets currentLoc
        modify (\st -> st { currentLoc = loc'''' + 1 })
        let elementReg = Register loc'''' (llvmType typ)
        let ins'''' = Load elementReg elementPtr
        addToCurrentBlock ins''''
        -- store array element in variable
        addToCurrentBlock (Store elementReg reg)
        -- compile stmt with new variable
        prevVars <- gets localVars
        modify (\st -> st { localVars = Data.Map.insert ident reg prevVars })
        body <- compile stmt
        modify (\st -> st { localVars = prevVars })
        -- increment index
        loc''''' <- gets currentLoc
        modify (\st -> st { currentLoc = loc''''' + 1 })
        let indexReg'' = Register loc''''' I32Type
        let ins''''' = Custom (show indexReg'' ++ " = add i32 " ++ show indexReg' ++ ", 1")
        addToCurrentBlock ins'''''
        addToCurrentBlock (Store indexReg'' indexReg)
        -- jump back to cond
        addToCurrentBlock (Custom $ "br label " ++ condLabel)
        bodyEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] [Label $ tail condLabel]})
        return $ prevEndBlock : llvmCodeExp ++ condEndBlock : body ++ [bodyEndBlock]


getRawString :: Value -> IM ([BasicBlock], Value)
getRawString (StringLiteral ind length) = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (PointerType I8Type)
    let ins = Custom (show returnReg ++ " = getelementptr inbounds [" ++ show length ++ " x i8], [" ++ show length ++ " x i8]* @strings" ++ show ind ++ ", i32 0, i32 0\n")
    addToCurrentBlock ins
    return ([], returnReg)
getRawString reg@(Register loc (PointerType I8Type)) = return ([], reg)
getRawString c = error $ "Internal compiler error: trying to get raw string from non-pointer: " ++ show (llvmType c)

concatStrings :: Expr -> Expr -> IM ([BasicBlock], Value)
concatStrings expr1 expr2 = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    (loadCode1, val1') <- getRawString val1
    (loadCode2, val2') <- getRawString val2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (PointerType I8Type)
    let ins = Custom (show returnReg ++ " = call i8* @__internal_concat(i8* " ++ show val1' ++ ", i8* " ++ show val2' ++ ")\n")
    addToCurrentBlock ins
    return (
        llvmCode1 ++ llvmCode2 ++ loadCode1 ++ loadCode2, returnReg
        )

compileExpr :: Expr -> IM ([BasicBlock], Value)
compileExpr (ECast _ t toknull) = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (llvmType t)
    let ins = Custom (show returnReg ++ " = bitcast i8* null to " ++ show (llvmType t) ++ "\n")
    addToCurrentBlock ins
    return ([], returnReg)
compileExpr (ELitNull _) = do
    return ([], ConstValue Nullptr)
compileExpr (EMethodApply _ expr method args) = do
    (llvmCode, val) <- compileExpr expr
    -- val is Pointer to a class, i.e. Pointer to Pointer to Vtable
    let clsName = case llvmType val of
            PointerType (ClassType clsName) -> clsName
            _ -> error "Internal compiler error: trying to call method on non-class"

    compiledArgs <- traverse compileExpr args
    let llvmCodeArgs = mconcat . map fst $ compiledArgs
    let argVals' = map snd compiledArgs
    let argTypes' = map llvmType argVals'
    -- insert self argument
    let argVals'' = val : argVals'
    -- let argTypes'' = PointerType (ClassType clsName) : argTypes'


    let clsname = case val of
            Register _ (PointerType (ClassType clsName)) -> clsName
            _ -> error "Internal compiler error: trying to call method on non-class"

    -- first entry of an object is pointer to vtable
    loc0 <- gets currentLoc
    modify (\st -> st { currentLoc = loc0 + 1 })
    let vtablePtrReg' = Register loc0 (PointerType $ PointerType $ ClassVtableType clsname)
    let ins0 = Custom (show vtablePtrReg' ++ " = getelementptr inbounds " ++ show (ClassType clsname) ++ ", " ++ show (PointerType $ ClassType clsname) ++ " " ++ show val ++ ", i32 0, i32 0 ; get addr of vtable ptr field\n")

    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let vtablePtrReg = Register loc (PointerType $ ClassVtableType clsname)
    let ins = Custom (show vtablePtrReg ++ " = load " ++ show (PointerType $ ClassVtableType clsname) ++ ", " ++ show (PointerType $ PointerType $ ClassVtableType clsname) ++ " " ++ show vtablePtrReg' ++ " ; load actual vtable ptr\n")

    classes' <- asks classes
    -- this will be a PointerType $ FunctionType retType argTypes
    let methodPtrType' = getMethodType2 clsname method classes'
    let methodPtrType = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodPtrType'
    let methodIndex' = getMethodIndex clsname method classes'
    let methodIndex = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodIndex'

    -- insert here calculation?
    -- optionally, bitcast everything. this is incorrect! we have to 
    -- bitcast to virtual class arguments i think? so dynamically obtain
    -- the superclass needed
    -- argtypes = dynamic
    let argTypes'' = case methodPtrType of
            PointerType (FunctionType _ argTypes) -> argTypes
            _ -> error "Internal compiler error: method pointer type has a wrong type"
    argVals <- zipWithM optionallyBitcast argTypes'' argVals''
    let argsStr = Data.List.intercalate ", " $ zipWith (\ argType argVal -> show argType ++ " " ++ show argVal) argTypes'' argVals

    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let methodPtrPtrReg = Register loc2 (PointerType methodPtrType)
    let ins2 = Custom (show methodPtrPtrReg ++ " = getelementptr inbounds " ++ show (ClassVtableType clsname) ++ ", " ++ show (PointerType $ ClassVtableType clsname) ++ " " ++ show vtablePtrReg ++ ", i32 0, i32 " ++ show methodIndex ++ " ; calculate address of the method pointer field in the vtable\n")

    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let methodPtrReg = Register loc3 methodPtrType
    let ins3 = Custom (show methodPtrReg ++ " = load " ++ show methodPtrType ++ ", " ++ show (PointerType methodPtrType) ++ " " ++ show methodPtrPtrReg ++ " ; load the actual method pointer\n")

    let funRetType = case methodPtrType of
            PointerType (FunctionType retType _) -> retType
            _ -> error "Internal compiler error: method pointer type has a wrong type"

    loc4 <- gets currentLoc
    modify (\st -> st { currentLoc = loc4 + 1 })
    let returnReg = Register loc4 funRetType
    let ins4 = case funRetType of
            VoidType -> "call " ++ show funRetType ++ " " ++ show methodPtrReg ++ "(" ++ argsStr ++ ")\n"
            _ -> show returnReg ++ " = call " ++ show funRetType ++ " " ++ show methodPtrReg ++ "(" ++ argsStr ++ ")\n"

    addToCurrentBlock ins0
    addToCurrentBlock ins
    addToCurrentBlock ins2
    addToCurrentBlock ins3
    addToCurrentBlock (Custom ins4)
    return (llvmCode ++ llvmCodeArgs, returnReg)

compileExpr (EApp _ i@(Ident ident) args) = do
    compiledArgs' <- traverse compileExpr args
    let llvmCode' = mconcat . map fst $ compiledArgs'
    let newArgs' = map snd compiledArgs'

    env <- ask
    -- to nie dziala, nie ma insertu self
    ((retType, argTypes), realName, newArgs, llvmCode) <- do
        case Data.Map.lookup i (functions env) of
            Just x -> return (x, ident, newArgs', llvmCode')
            Nothing -> do
                let classes' = classes env
                let currentClas = currentClass env
                case currentClas of
                    Just cls -> do
                        self' <- getVarValue (Ident "self")
                        (code, self) <- dereference self'
                        case getMethodType22 cls i classes' of
                            Just (PointerType (FunctionType retType argTypes), realMethName) -> return ((retType, argTypes), tail realMethName, self : newArgs', llvmCode' ++ code)
                            Nothing -> error $ "Nothing Internal compiler error: function not found: " ++ show i
                            _ -> error "Else Internal compiler error: function not found"


    -- if needed, bitcast every argument to superclass
    compiledArgs <- mapM (\(argType, argVal) -> do
            ret <- optionallyBitcast argType argVal
            return (argType, ret)
            ) $ zip argTypes newArgs

    let argVals = map snd compiledArgs
    -- add types to arguments
    let argsWithTypes = zip argTypes argVals
    let argsStr = Data.List.intercalate ", " $ map (\(argType, argVal) -> show argType ++ " " ++ show argVal) argsWithTypes

    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnRegister = Register loc retType
    let ins = case retType of
            VoidType -> "call " ++ show retType ++ " @" ++ realName ++ "(" ++ argsStr ++ ")\n"
            _ -> show returnRegister ++ " = call " ++ show retType ++ " @" ++ realName ++ "(" ++ argsStr ++ ")\n"
    addToCurrentBlock (Custom ins)
    return (llvmCode, returnRegister)

compileExpr (ELVal _ lval) = do
    (llvmCode, val) <- compileLVal lval
    (loadCode, valLoaded) <- dereference val
    return (llvmCode ++ loadCode, valLoaded)

compileExpr (ERel _ expr1 op expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2') <- compileExpr expr2
    val2 <- optionallyBitcast (llvmType val1) val2'
    let argType = llvmType val1
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc I1Type
    case llvmType val1 of
        PointerType I8Type -> do
            let ins = Custom (show returnReg ++ " = call i1 @__internal_strcmp(i8* " ++ show val1 ++ ", i8* " ++ show val2 ++ ")\n")
            addToCurrentBlock ins
            case op of
                OpNe _ -> return (llvmCode1 ++ llvmCode2, returnReg)
                OpEq _ -> do
                    loc <- gets currentLoc
                    modify (\st -> st { currentLoc = loc + 1 })
                    let returnReg2 = Register loc I1Type
                    let ins2 = Custom (show returnReg2 ++ " = xor i1 1, " ++ show returnReg ++ "\n")
                    addToCurrentBlock ins2
                    return (llvmCode1 ++ llvmCode2, returnReg2)
                _ -> error "Internal compiler error: only == and != supported for strings"
        _ -> do
            let ins = Custom (show returnReg ++ " = icmp " ++ case op of
                    OpLt _ -> "slt"
                    OpLe _ -> "sle"
                    OpGt _ -> "sgt"
                    OpGe _ -> "sge"
                    OpEq _ -> "eq"
                    OpNe _ -> "ne"
                    ++ " " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n")
            addToCurrentBlock ins
            return (llvmCode1 ++ llvmCode2, returnReg)

compileExpr (ENeg _ expr) = do
    (llvmCode, val) <- compileExpr expr
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (llvmType val)
    let ins = Custom (show returnReg ++ " = sub " ++ show (llvmType val) ++ " 0, " ++ show val ++ "\n")
    addToCurrentBlock ins
    return (llvmCode, returnReg)
compileExpr (EAdd _ expr1 op expr2) = do
    stateBefore <- get
    (llvmCode1, val1) <- compileExpr expr1
    case val1 of
        StringLiteral _ _ -> do
            put stateBefore
            concatStrings expr1 expr2
        Register _ (PointerType I8Type) -> do
            put stateBefore
            concatStrings expr1 expr2
        _ -> do
            (llvmCode2, val2) <- compileExpr expr2
            let argType = llvmType val1

            let llvmCode = llvmCode1 ++ llvmCode2
            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let returnReg = Register loc argType
            let ins = case op of
                    OpAdd _ -> Custom (show returnReg ++ " = add " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n")
                    OpSub _ -> Custom (show returnReg ++ " = sub " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n")
            addToCurrentBlock ins
            return (llvmCode, returnReg)
compileExpr (EMul _ expr1 op expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    let argType = llvmType val1
    let llvmCode = llvmCode1 ++ llvmCode2
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc argType
    let opcode = case op of
            OpMul _ -> "mul"
            OpDiv _ -> "sdiv"
            OpMod _ -> "srem"
    let ins = Custom (show returnReg ++ " = " ++ opcode ++ " " ++ show argType ++ " " ++ show val1 ++ ", " ++ show val2 ++ "\n")
    addToCurrentBlock ins
    return (llvmCode, returnReg)

compileExpr (ELitInt _ int) = pure ([], ConstValue (I32 int))
compileExpr (EString _ str) = do
    ind <- addNewString str
    return ([], StringLiteral ind (toInteger $ length str + 1))
compileExpr (ELitTrue _) = pure ([], ConstValue (I1 True))
compileExpr (ELitFalse _) = pure ([], ConstValue (I1 False))
compileExpr (ENot _ expr) = do
    (llvmCode, val) <- compileExpr expr
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc I1Type
    let ins = Custom (show returnReg ++ " = xor i1 1, " ++ show val ++ "\n")
    addToCurrentBlock ins
    return (llvmCode, returnReg)
compileExpr (EOr _ expr1 _ expr2) = do
    (code, val) <- compileExpr (ENot BNFC'NoPosition (EAnd BNFC'NoPosition (ENot BNFC'NoPosition expr1) (OpAnd BNFC'NoPosition) (ENot BNFC'NoPosition expr2)))
    return (code, val)
compileExpr (EAnd _ expr1 _ expr2) = do
    (llvmCode1, val1) <- compileExpr expr1

    labelAnd <- gets currentLabel
    let labelStart = "%andStart" ++ show labelAnd
    let labelCheckSecond = "%andCheckSecond" ++ show labelAnd
    let labelCheckSecondEnd = "%andCheckSecondEnd" ++ show labelAnd
    let labelEnd = "%andEnd" ++ show labelAnd
    modify (\st -> st { currentLabel = labelAnd + 1 })

    addToCurrentBlock (Custom ("br label " ++ labelStart ++ "\n"))
    expr1Block <- gets currentBlock
    predecessor <- getLabelOfCurrentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelStart)) [] [predecessor] })
    addToCurrentBlock (Custom ("br i1 " ++ show val1 ++ ", label " ++ labelCheckSecond ++ ", label " ++ labelEnd ++ "\n"))
    expr1BlockEnd <- gets currentBlock
    testBlock <- getLabelOfCurrentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelCheckSecond)) [] [testBlock] })
    (llvmCode2, val2) <- compileExpr expr2
    addToCurrentBlock (Custom ("br label " ++ labelCheckSecondEnd ++ "\n"))
    expr2BlockEnd <- gets currentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelCheckSecondEnd)) [] [Label $ tail labelCheckSecond] })
    addToCurrentBlock (Custom ("br label " ++ labelEnd ++ "\n"))
    expr2BlockEndEnd <- gets currentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelEnd)) [] [testBlock, Label $ tail labelCheckSecondEnd] })

    resultLoc <- gets currentLoc
    modify (\st -> st { currentLoc = resultLoc + 1 })
    let returnReg = Register resultLoc I1Type
    addToCurrentBlock (Custom $ show returnReg ++ " = phi i1 [ false, " ++ labelStart ++ " ], [ " ++ show val2 ++ ", " ++ labelCheckSecondEnd ++ " ]")
    return (llvmCode1 ++ expr1Block : llvmCode2 ++ [expr1BlockEnd, expr2BlockEnd, expr2BlockEndEnd], returnReg)

compileExpr (ENewArr _ type_ expr) = do
    -- get arr length
    (llvmCode, val) <- compileExpr expr

    -- multiply by 8 to get size
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let sizeReg' = Register loc I32Type
    let ins = Custom (show sizeReg' ++ " = mul i32 " ++ show val ++ ", 8")
    addToCurrentBlock ins

    -- add 16 to size to store length and data ptr
    loc' <- gets currentLoc
    modify (\st -> st { currentLoc = loc' + 1 })
    let sizeReg = Register loc' I32Type
    let ins' = Custom (show sizeReg ++ " = add i32 " ++ show sizeReg' ++ ", 16")
    addToCurrentBlock ins'

    -- allocate memory
    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let callocReg = Register loc2 (PointerType I8Type)
    let callocCode = Custom (show callocReg ++ " = call i8*  @__calloc(i32 " ++ show sizeReg ++ ")")
    addToCurrentBlock callocCode

    -- prepare result
    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let returnReg = Register loc3 (PointerType $ ArrType $ llvmType type_)
    let bitcast = Custom (show returnReg ++ " = bitcast i8* " ++ show callocReg ++ " to " ++ show (PointerType $ ArrType $ llvmType type_))
    addToCurrentBlock bitcast
    -- let alloca = Custom (show returnReg ++ " = alloca %Array")
    -- addToCurrentBlock alloca

    -- get length field pointer
    loc4 <- gets currentLoc
    modify (\st -> st { currentLoc = loc4 + 1 })
    let lenFieldPtr = Register loc4 (PointerType I32Type)
    let lenFieldPtrIns = Custom (show lenFieldPtr ++ " = getelementptr %Array, %Array* " ++ show returnReg ++ ", i32 0, i32 0")
    addToCurrentBlock lenFieldPtrIns
    -- store length in struct
    let storeLen = Custom ("store i32 " ++ show val ++ ", i32* " ++ show lenFieldPtr)
    addToCurrentBlock storeLen

    -- get data field pointer
    loc5 <- gets currentLoc
    modify (\st -> st { currentLoc = loc5 + 1 })
    let dataFieldPtr = Register loc5 (PointerType $ PointerType $ llvmType type_)
    let dataFieldPtrIns = Custom (show dataFieldPtr ++ " = getelementptr %Array, %Array* " ++ show returnReg ++ ", i32 0, i32 1")
    addToCurrentBlock dataFieldPtrIns
    -- store data in struct
    loc6 <- gets currentLoc
    modify (\st -> st { currentLoc = loc6 + 1 })
    let dataPtr = Register loc6 (PointerType I8Type)
    let dataPtrIns = Custom (show dataPtr ++ " = getelementptr i8, i8* " ++ show callocReg ++ ", i32 16")
    addToCurrentBlock dataPtrIns
    let storeData = Custom ("store i8* " ++ show dataPtr ++ ", i8** " ++ show dataFieldPtr)
    addToCurrentBlock storeData

    return (llvmCode, returnReg)

compileExpr (ENew _ ident@(Ident i)) = do
    classes' <- asks classes
    let class_ = case Data.Map.lookup ident classes' of
            Just cls -> cls
            Nothing -> error $ "Internal compiler error: class " ++ show ident ++ " not found"

    -- use malloc to allocate memory for the object
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let callocReg = Register loc (PointerType I8Type)
    let callocCode = Custom (show callocReg ++ " = call i8*  @__calloc(i32 " ++ show (classSize class_) ++ ")\n")

    -- bitcast
    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let bitcastReg = Register loc2 (PointerType (ClassType ident))
    let bitcastCode = Custom (show bitcastReg ++ " = bitcast i8* " ++ show callocReg ++ " to " ++ show (PointerType (ClassType ident)) ++ "\n")

    -- store pointer to correct vtable
    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let vtablePtrReg = Register loc3 (PointerType $ PointerType (ClassVtableType ident))
    let vtableFetchCode = Custom (show vtablePtrReg ++ " = getelementptr inbounds " ++ show (ClassType ident) ++ ", " ++ show (PointerType (ClassType ident)) ++ " " ++ show bitcastReg ++ ", i32 0, i32 0\n")

    -- store vtable in allocated object
    let storeCode = Custom ("store " ++ show (PointerType (ClassVtableType ident)) ++ " @vtable." ++ i ++ ", " ++ show (PointerType (PointerType (ClassVtableType ident))) ++ " " ++ show vtablePtrReg ++ "\n")
    addToCurrentBlock callocCode
    addToCurrentBlock bitcastCode
    addToCurrentBlock vtableFetchCode
    addToCurrentBlock storeCode

    -- default-initialize strings if any
    mapM_ (\ (Ident attrName, attrType) -> case attrType of
        PointerType I8Type -> do
            emptyString <- addNewString ""
            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let attrFieldPtr = Register loc (PointerType $ PointerType I8Type)
            let attrInd = case getAttrIndex ident (Ident attrName) classes' of
                    Just ind -> ind
                    Nothing -> error $ "Internal compiler error: attribute " ++ show attrName ++ " not found in class " ++ show ident
            let ins = Custom (show attrFieldPtr ++ " = getelementptr inbounds " ++ show (ClassType ident) ++ ", " ++ show (PointerType (ClassType ident)) ++ " " ++ show bitcastReg ++ ", i32 0, i32 " ++ show (attrInd) ++ "\n")
            addToCurrentBlock ins
            addToCurrentBlock $ Store (StringLiteral emptyString 1) attrFieldPtr
            return ()
        _ -> return ()) (fields class_)
    return ([], bitcastReg)


getVarValue :: Ident -> IM Value
getVarValue ident = do
    env <- ask
    localVars <- gets localVars
    case Data.Map.lookup ident (var env) of
        Just val -> return val
        Nothing -> case Data.Map.lookup ident localVars of
            Just val -> return val
            Nothing -> do
                -- try get attribute
                cls <- asks currentClass
                case cls of
                    Nothing -> error "Internal compiler error: no current class"
                    Just cls -> do
                        let class_ = case Data.Map.lookup cls (classes env) of
                                Just cls -> cls
                                Nothing -> error $ "Internal compiler error: class " ++ show cls ++ " not found"

                        let attrInd' = getAttrIndex cls ident (classes env)
                        let attrInd = case attrInd' of
                                Just ind -> ind
                                Nothing -> error $ "Internal compiler error: attribute " ++ show ident ++ " not found in class " ++ show cls
                        let attrType' = getAttrType3 cls ident (classes env)
                        let attrType = case attrType' of
                                Just t -> t
                                Nothing -> error $ "Internal compiler error: attribute " ++ show ident ++ " not found in class " ++ show cls

                        loc <- gets currentLoc
                        modify (\st -> st { currentLoc = loc + 1 })
                        let returnReg = Register loc (PointerType attrType)
                        let ins = Custom (show returnReg ++ " = getelementptr inbounds " ++ show (ClassType cls) ++ ", " ++ show (PointerType $ ClassType cls) ++ " %self, i32 0, i32 " ++ show attrInd ++ "\n")
                        addToCurrentBlock ins
                        return returnReg

-- it returns a register containing the address of the lvalue
compileLVal :: LVal -> IM ([BasicBlock], Value)
compileLVal (LVar _ (Ident ident)) = do
    env <- ask
    varValue <- getVarValue (Ident ident)
    return ([], varValue)
compileLVal (LArrAcc _ expr1 expr2) = do
    (llvmCode1, val1ptr) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    let eltType = case llvmType val1ptr of
            PointerType (ArrType t) -> t
            _ -> error "Internal compiler error: trying to access array element of non-array"

    -- get data pointer field address
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let dataPtrReg = Register loc (PointerType $ PointerType I8Type)
    let ins = Custom (show dataPtrReg ++ " = getelementptr inbounds %Array, %Array* " ++ show val1ptr ++ ", i32 0, i32 1")
    -- load data pointer
    loc2 <- gets currentLoc
    modify (\st -> st { currentLoc = loc2 + 1 })
    let dataPtrReg' = Register loc2 (PointerType I8Type)
    let ins2 = Custom (show dataPtrReg' ++ " = load i8*, i8** " ++ show dataPtrReg)
    -- bitcast to correct type
    loc3 <- gets currentLoc
    modify (\st -> st { currentLoc = loc3 + 1 })
    let dataPtrReg'' = Register loc3 (PointerType eltType)
    let ins3 = Custom (show dataPtrReg'' ++ " = bitcast i8* " ++ show dataPtrReg' ++ " to " ++ show (PointerType eltType))

    -- get element address
    loc4 <- gets currentLoc
    modify (\st -> st { currentLoc = loc4 + 1 })
    let elementPtrReg = Register loc4 (PointerType eltType)
    let ins4 = Custom (show elementPtrReg ++ " = getelementptr " ++ show eltType ++ ", " ++ show (PointerType eltType) ++ " " ++ show dataPtrReg'' ++ ", i32 " ++ show val2)
    addToCurrentBlock ins
    addToCurrentBlock ins2
    addToCurrentBlock ins3
    addToCurrentBlock ins4
    return (llvmCode1 ++ llvmCode2, elementPtrReg)


compileLVal (LAttrAcc _ expr (Ident ident)) = do
    (llvmCode, val) <- compileExpr expr
    case llvmType val of
        PointerType (ArrType t) -> case ident of
            "length" -> do
                loc <- gets currentLoc
                modify (\st -> st { currentLoc = loc + 1 })
                let lengthPtr = Register loc (PointerType I32Type)
                let ins = Custom (show lengthPtr ++ " = getelementptr inbounds %Array, %Array* " ++ show val ++ ", i32 0, i32 0\n")
                addToCurrentBlock ins

                -- dont dereference, as compileLVal should return a pointer to the
                -- actual value
                -- loc2 <- gets currentLoc
                -- modify (\st -> st { currentLoc = loc2 + 1 })
                -- let returnReg = Register loc2 I32Type
                -- let ins2 = Custom (show returnReg ++ " = load i32, i32* " ++ show lengthPtr ++ "\n")
                -- addToCurrentBlock ins2
                -- return (llvmCode, returnReg)
                return (llvmCode, lengthPtr)
            _ -> error "Internal compiler error: trying to access attribute of non-class"
        PointerType (ClassType classType) -> do
            env <- ask
            let attrInd' = getAttrIndex classType (Ident ident) (classes env)
            let attrInd = case attrInd' of
                    Just ind -> ind
                    Nothing -> error $ "Internal compiler error: attribute " ++ show ident ++ " not found in class " ++ show classType
            let attrType' = getAttrType3 classType (Ident ident) (classes env)
            let attrType = case attrType' of
                    Just t -> t
                    Nothing -> error $ "Internal compiler error: attribute " ++ show ident ++ " not found in class " ++ show classType

            loc <- gets currentLoc
            modify (\st -> st { currentLoc = loc + 1 })
            let returnReg = Register loc (PointerType attrType)
            let ins = Custom (show returnReg ++ " = getelementptr inbounds " ++ show (ClassType classType) ++ ", " ++ show (PointerType $ ClassType classType) ++ " " ++ show val ++ ", i32 0, i32 " ++ show attrInd ++ "\n")
            addToCurrentBlock ins
            return (llvmCode, returnReg)
        _ -> error "Internal compiler error: trying to access attribute of non-class"
