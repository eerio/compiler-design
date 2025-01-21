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
import Data.Sequence (singleton, Seq, intersperse)
import Control.Monad.State (State, StateT (runStateT), runState, gets, modify, put, get)
import Control.Monad.Writer (WriterT (runWriterT))
import qualified Data.Foldable
import qualified Control.Monad.RWS as Data.Sequence
import qualified Data.List
import Data.Maybe (Maybe, fromMaybe, maybeToList)
import Data.Foldable (toList, traverse_)
import Data.Char(ord)
import Numeric(showHex)
import Text.ParserCombinators.ReadP (char)
import Data.Graph (Graph, Vertex, graphFromEdges, topSort)


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
    methods :: [(Ident, PrimitiveType)]
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

processClass :: Map Ident Class -> ClsDefC -> Map Ident Class
processClass acc cls =
    let inheritedFields  = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . fields)) (getParentName cls)
        inheritedMethods = maybe [] (\p -> fromMaybe [] (Data.Map.lookup p acc >>= Just . methods)) (getParentName cls)
        newClass = Class (getParentName cls) (inheritedFields ++ getAttrTypes cls) (inheritedMethods ++ getMethodTypes cls)
    in Data.Map.insert (getClassName cls) newClass acc

createClassMap :: [ClsDefC] -> Map Ident Class
createClassMap clsDefs =
    let (graph, nodeFromVertex, _) = graphFromEdges [(cls, getClassName cls, maybeToList (getParentName cls)) | cls <- clsDefs]
        sortedVertices = topSort graph
        sortedClasses = map (\v -> let (cls, _, _) = nodeFromVertex v in cls) sortedVertices
    in foldl processClass Data.Map.empty sortedClasses

classSize :: Class -> Integer
classSize cls = do
    let fields' = fields cls
    8 + 8 * toInteger (length fields')

getMethodType2 :: Ident -> Ident -> Map Ident Class -> Maybe PrimitiveType
getMethodType2 className methodName classMap =
    Data.Map.lookup className classMap >>= \(Class _ _ methods) -> Data.List.lookup methodName methods

-- Function to retrieve method index in the vtable
getMethodIndex :: Ident -> Ident -> Map Ident Class -> Maybe Int
getMethodIndex className methodName classMap =
    Data.Map.lookup className classMap >>= \(Class _ _ methods) ->
        let methodNames = map fst methods
        in Data.List.elemIndex methodName methodNames

-- getFunctionIdent :: Maybe Ident -> Ident -> Ident
-- getFunctionIdent Nothing (Ident name) = "@" ++ name

storeVtable :: Ident -> Value -> IM (Data.Sequence.Seq String)
storeVtable ident@(Ident i) objReg = do
    let vtable = "@vtable." ++ i
    return $ singleton ("store " ++ show (PointerType (ClassVtableType ident)) ++ " " ++ vtable ++ ", " ++ show (PointerType (PointerType (ClassVtableType ident))) ++ " " ++ show objReg ++ "\n")

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

addSelfArgumentsCls :: ClsDefC -> ClsDefC
addSelfArgumentsCls (ClsDef pos ident mems) = ClsDef pos ident (map (addSelfArgumentsClsMem ident) mems)
addSelfArgumentsCls (ClsDefExt pos ident parent mems) = ClsDefExt pos ident parent (map (addSelfArgumentsClsMem ident) mems)

addSelfArguments :: [TopDefC] -> [TopDefC]
addSelfArguments [] = []
addSelfArguments (f@(FunDefTop pos funDef) : rest) = f : addSelfArguments rest
addSelfArguments (ClsDefTop pos clsDef : rest) = ClsDefTop pos (addSelfArgumentsCls clsDef) : addSelfArguments rest

createVtable :: ClsDefC -> IM String
createVtable cls@(ClsDef _ (Ident clsName) mems) = do
    let methods = getMethodTypes cls
    let vtableType = "%vtable." ++ clsName ++ ".type = type { " ++ Data.List.intercalate ", " (map (show . snd) methods) ++ " }\n"
    let vtable = "@vtable." ++ clsName ++ " = global %vtable." ++ clsName ++ ".type { " ++ Data.List.intercalate ", " (map f methods) ++ " }\n"
    let structName = "%class." ++ clsName
    let vtable_ptr = ["%vtable." ++ clsName ++ ".type*"]
    let members = getAttrTypes cls
    let structDecl = unlines [
            structName ++ " = type { ",
            Data.List.intercalate ", " (vtable_ptr ++ map (show . snd) members),
            "}"
            ]
    return $ vtableType ++ vtable ++ structDecl ++ "\n"
    where
        f (Ident ident, type_) = show type_ ++ " " ++ "@" ++ clsName ++ "_" ++ ident
createVtable (ClsDefExt p i _ mems) = createVtable (ClsDef p i mems)

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
            "declare i8* @__calloc(i32)"
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

        allStrings <- gets strings
        let prepString rawStr = "\"" ++ concatMap charToHex rawStr ++ "\\00\""
        let llvmStrings = unlines $ map (\(str, ind) -> "@strings" ++ show ind ++ " = private constant [" ++ show (length str + 1) ++ " x i8] c" ++ prepString str ++ "\n") $ Data.Map.toList allStrings

        let basicBlock = BasicBlock Nothing [Custom llvmStrings] []
        return $ basicBlock : code

instance Compilable TopDefC where
    compile (FunDefTop _ def) = compile def
    compile (ClsDefTop _ def) = compile def

instance Compilable ClsDefC where
    compile c@(ClsDef _ i@(Ident nam) mems) = do
        vtable <- createVtable c
        let block = BasicBlock Nothing [Custom vtable] []
        env <- ask
        results <- traverse (local (const env {currentClass = Just i}) . compile) mems
        return $ block : mconcat results
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

instance Compilable FunDefC where
    compile (FunDef _ retType_ (Ident name) args block@(Block _ stmts)) = do
        -- prevBlock <- gets currentBlock

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


        lab <- gets currentLabel
        modify (\st -> st { currentLabel = lab + 1 })
        let openingLabel = Label $ "entry" ++ show lab

        let headerBlock = BasicBlock Nothing [header] []
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
                PointerType p -> SRetExp BNFC'NoPosition (EString BNFC'NoPosition "")
                _ -> error "Internal compiler error: no return type"
        let block' = Block BNFC'NoPosition (stmts ++ [retStmt])
        basicblocks <- local (\env -> env { returnType = Just retType, var = newVars }) $ do
            compile block'

        let endblock = BasicBlock Nothing [Custom "", Custom "}"] []
        return $ (headerBlock  : basicblocks) ++ [endblock]
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
    _ -> error "Internal compiler error: trying to dereference non-pointer"

dereferenceType :: Value -> PrimitiveType
dereferenceType (Register _ (PointerType p)) = p
dereferenceType _ = error "Internal compiler error: trying to dereference non-pointer"

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
    show (Custom str) = str

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
        addToCurrentBlock (Ret val)
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
                addToCurrentBlock (Store val reg)
                return llvmCode
            declareItem (DeclNoInit _ ident) = do
                reg <- getNewRegister (PointerType $ llvmType decltype)
                modify (\st -> st { localVars = Data.Map.insert ident reg (localVars st) })
                addToCurrentBlock (Alloca reg)
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
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condTrueLabel)  [] []})
        thenBlocks <- compile stmt1
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        thenEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condFalseLabel) [] []})
        elseBlocks <- compile stmt2
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        elseEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] []})
        return $ condBlocks ++ condEndBlock : thenBlocks ++ thenEndBlock : elseBlocks ++ [elseEndBlock]

    compile (SCond _ exp stmt) = do
        (condBlocks, val) <- compileExpr exp

        condLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = condLabelN + 1 })
        let condTrueLabel = "%condTrue" ++ show condLabelN
        let endLabel = "%condEnd" ++ show condLabelN

        addToCurrentBlock (Custom $ "br i1" ++ show val ++ ", label " ++ condTrueLabel ++ ", label " ++ endLabel ++ "\n")
        condEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condTrueLabel) [] []})
        thenBlocks <- compile stmt
        addToCurrentBlock (Custom $ "br label " ++ endLabel ++ "\n")
        thenEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] []})
        return $ condBlocks ++ condEndBlock : thenBlocks ++ [thenEndBlock]

    compile (SAss _ lval exp) = do
        (llvmCodeLVal, valLVal) <- compileLVal lval
        (llvmCodeExp, valExp) <- compileExpr exp
        addToCurrentBlock $ Store valExp valLVal
        return $ llvmCodeLVal ++ llvmCodeExp
    compile (SWhile _ exp stmt) = do
        loopLabelN <- gets currentLabel
        modify (\st -> st { currentLabel = loopLabelN + 1 })
        let condLabel = "%loopCond" ++ show loopLabelN
        let loopLabel = "%loop" ++ show loopLabelN
        let endLabel = "%loopEnd" ++ show loopLabelN
        addToCurrentBlock (Custom $ "br label " ++ condLabel ++ "\n")
        prevEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail condLabel) [] []})
        (condCode, val) <- compileExpr exp
        addToCurrentBlock (Custom $ "br i1 " ++ show val ++ ", label " ++ loopLabel ++ ", label " ++ endLabel ++ "\n")
        condEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail loopLabel) [] []})
        body <- compile stmt
        addToCurrentBlock (Custom $ "br label " ++ condLabel ++ "\n")
        bodyEndBlock <- gets currentBlock
        modify (\st -> st { currentBlock = BasicBlock (Just $ Label $ tail endLabel) [] []})
        return $ prevEndBlock : condCode ++ condEndBlock : body ++ [bodyEndBlock]

getRawString :: Value -> IM ([BasicBlock], Value)
getRawString (StringLiteral ind length) = do
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc (PointerType I8Type)
    let ins = Custom (show returnReg ++ " = getelementptr inbounds [" ++ show length ++ " x i8], [" ++ show length ++ " x i8]* @strings" ++ show ind ++ ", i32 0, i32 0\n")
    addToCurrentBlock ins
    return ([], returnReg)
getRawString reg@(Register loc (PointerType I8Type)) = return ([], reg)

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
-- compileExpr (EMethodApply _ expr method args) = do
--     (llvmCode, val) <- compileExpr expr
--     compiledArgs <- traverse compileExpr args
--     let llvmCodeArgs = mconcat . map fst $ compiledArgs
--     let argVals = map snd compiledArgs
--     let argTypes = map llvmType argVals
--     let argsStr = Data.List.intercalate ", " $ zipWith (\ argType argVal -> show argType ++ " " ++ show argVal) argTypes argVals

--     let clsname = case val of
--             Register _ (PointerType (ClassType clsName)) -> clsName
--             _ -> error "Internal compiler error: trying to call method on non-class"

--     -- first entry of an object is pointer to vtable
--     loc <- gets currentLoc
--     modify (\st -> st { currentLoc = loc + 1 })
--     let vtablePtrReg = Register loc (PointerType (ClassVtableType clsname))
--     classes' <- classes <$> ask
--     let methodType' = getMethodType2 clsname method classes'
--     let methodType = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodType'
--     let methodIndex' = getMethodIndex clsname method classes'
--     let methodIndex = fromMaybe (error ("Internal compiler error: method not found" ++ show classes' ++ "\n " ++ show clsname ++ " " ++ show method)) methodIndex'
--     let codeGetVtablePtr = singleton (show vtablePtrReg ++ " = getelementptr " ++ show (ClassType clsname) ++ ", " ++ show (PointerType (ClassType clsname)) ++ " " ++ show val ++ ", i32 0, i32 0\n")
--     loc2 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc2 + 1 })
--     let vtableReg = Register loc2 (ClassVtableType clsname)
--     let codeLoadVtable = singleton (show vtableReg ++ " = load " ++ show (PointerType (ClassVtableType clsname)) ++ ", " ++ show (PointerType (PointerType (ClassVtableType clsname))) ++ " " ++ show vtablePtrReg ++ "\n")
--     loc3 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc3 + 1 })
--     let methodPtrReg = Register loc3 (PointerType methodType)
--     let getMethodPtr = singleton (show methodPtrReg ++ " = getelementptr " ++ show (ClassVtableType clsname) ++ ", " ++ show (PointerType (ClassVtableType clsname)) ++ " " ++ show vtableReg ++ ", i32 0, i32 " ++ show methodIndex ++ "\n")
--     loc4 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc4 + 1 })
--     let methodReg = Register loc4 methodType
--     let loadMethod = singleton (show methodReg ++ " = load " ++ show (PointerType methodType) ++ ", " ++ show (PointerType (PointerType methodType)) ++ " " ++ show methodPtrReg ++ "\n")
--     loc5 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc5 + 1 })
--     let returnRegister = Register loc (PointerType I8Type)
--     env <- ask
--     let methodReturnType = case methodType of
--             FunctionType retType _ -> retType
--             _ -> error "Internal compiler error: method type is not a function"
--     let evalMethod = singleton (show returnRegister ++ " = call " ++ show (PointerType I8Type) ++ " " ++ show methodReg ++ "(" ++ show (PointerType (ClassType clsname)) ++ " " ++ show val ++ ", i8* " ++ show vtablePtrReg ++ ", " ++ argsStr ++ ")\n")
--     return (llvmCode <> llvmCodeArgs <> codeGetVtablePtr <> codeLoadVtable <> getMethodPtr <> loadMethod <> evalMethod, returnRegister)

compileExpr (EApp _ i@(Ident ident) args) = do
    compiledArgs <- traverse compileExpr args
    let llvmCode = mconcat . map fst $ compiledArgs
    -- take function types from environment
    env <- ask
    let argTypes = case Data.Map.lookup i (functions env) of
            Just (_, types) -> types
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"
    let retType = case Data.Map.lookup i (functions env) of
            Just (type_, _) -> type_
            Nothing -> error $ "Internal compiler error: function " ++ ident ++ " not found"

    let argVals = map snd compiledArgs
    -- add types to arguments
    let argsWithTypes = zip argTypes argVals
    let argsStr = Data.List.intercalate ", " $ map (\(argType, argVal) -> show argType ++ " " ++ show argVal) argsWithTypes

    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnRegister = Register loc retType
    let ins = case retType of
            VoidType -> "call " ++ show retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"
            _ -> show returnRegister ++ " = call " ++ show retType ++ " @" ++ ident ++ "(" ++ argsStr ++ ")\n"
    addToCurrentBlock (Custom ins)
    return (llvmCode, returnRegister)

compileExpr (ELVal _ lval) = do
    (llvmCode, val) <- compileLVal lval
    (loadCode, valLoaded) <- dereference val
    return (llvmCode ++ loadCode, valLoaded)

compileExpr (ERel _ expr1 op expr2) = do
    (llvmCode1, val1) <- compileExpr expr1
    (llvmCode2, val2) <- compileExpr expr2
    let argType = llvmType val1
    loc <- gets currentLoc
    modify (\st -> st { currentLoc = loc + 1 })
    let returnReg = Register loc I1Type
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

compileExpr (ELitNull _) = error "Not implemented: nulls "
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
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelStart)) [] [] })
    addToCurrentBlock (Custom ("br i1 " ++ show val1 ++ ", label " ++ labelCheckSecond ++ ", label " ++ labelEnd ++ "\n"))
    expr1BlockEnd <- gets currentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelCheckSecond)) [] [] })
    (llvmCode2, val2) <- compileExpr expr2
    addToCurrentBlock (Custom ("br label " ++ labelCheckSecondEnd ++ "\n"))
    expr2BlockEnd <- gets currentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelCheckSecondEnd)) [] [] })
    addToCurrentBlock (Custom ("br label " ++ labelEnd ++ "\n"))
    expr2BlockEndEnd <- gets currentBlock
    modify (\st -> st { currentBlock = BasicBlock (Just (Label $ tail labelEnd)) [] [] })

    resultLoc <- gets currentLoc
    modify (\st -> st { currentLoc = resultLoc + 1 })
    let returnReg = Register resultLoc I1Type
    addToCurrentBlock (Custom $ show returnReg ++ " = phi i1 [ false, " ++ labelStart ++ " ], [ " ++ show val2 ++ ", " ++ labelCheckSecondEnd ++ " ]")
    return (llvmCode1 ++ expr1Block : llvmCode2 ++ [expr1BlockEnd, expr2BlockEnd, expr2BlockEndEnd], returnReg)

compileExpr (ENewArr _ type_ expr) = error "Not implemented: new array"
-- compileExpr (ENew _ ident) = do
--     -- construct a default object of class ident
--     classes' <- classes <$> ask
--     let class_ = case Data.Map.lookup ident classes' of
--             Just cls -> cls
--             Nothing -> error $ "Internal compiler error: class " ++ show ident ++ " not found"
--     -- use malloc to allocate memory for the object
--     loc <- gets currentLoc
--     modify (\st -> st { currentLoc = loc + 1 })
--     let callocReg = Register loc (PointerType I8Type)
--     let callocCode = singleton (show callocReg ++ " = call i8*  @__calloc(i32 " ++ show (classSize class_) ++ ")\n")
--     -- bitcast
--     loc2 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc2 + 1 })
--     let bitcastReg = Register loc2 (PointerType (ClassType ident))
--     let bitcastCode = singleton (show bitcastReg ++ " = bitcast i8* " ++ show callocReg ++ " to " ++ show (PointerType (ClassType ident)) ++ "\n")
--     loc3 <- gets currentLoc
--     modify (\st -> st { currentLoc = loc3 + 1 })
--     let vtableReg = Register loc3 (PointerType (ClassVtableType ident))
--     let vtableFetchCode = singleton (show vtableReg ++ " = getelementptr inbounds " ++ show (ClassType ident) ++ ", " ++ show (PointerType (ClassType ident)) ++ " " ++ show bitcastReg ++ ", i32 0, i32 0\n")
--     -- store vtable in allocated object
--     storeCode <- storeVtable ident vtableReg
--     return (callocCode <> bitcastCode <> vtableFetchCode <> storeCode, bitcastReg)

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
compileLVal :: LVal -> IM ([BasicBlock], Value)
compileLVal (LVar _ (Ident ident)) = do
    env <- ask
    varValue <- getVarValue (Ident ident)
    return ([], varValue)
compileLVal (LArrAcc _ expr1 expr2) = error "Not implemented: array access"
compileLVal (LAttrAcc _ expr (Ident ident)) = error "Not implemented: attribute access"
