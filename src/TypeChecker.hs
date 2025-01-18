{-# LANGUAGE FlexibleInstances, LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}


module TypeChecker (typeCheck, CheckEnv, typeCheck_) where

import Latte.Par
import Latte.Abs
import Latte.Print
import Latte.ErrM
import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Data.Map (Map)
import Data.List (nub)
import qualified Data.Map as Map
import qualified Control.Monad
import System.IO (hPutStrLn, stderr)
import Control.Exception (throw)
import Data.Data (Typeable)
import Control.Exception.Base (Exception)
import GHC.Stack (HasCallStack)
import Control.Monad (foldM)
import qualified Data.Set as Data
import GHC.ResponseFile (expandResponse)
import System.Process (CreateProcess(env))

type TypeEnv = Map Ident Type

data CheckEnv = CheckEnv {
    typeEnv :: !TypeEnv,
    retType :: !(Maybe Type),
    inLoop :: !Bool,
    classes :: !(Map Ident (Maybe Ident, TypeEnv)),
    clsName :: !(Maybe Ident)
}

modifyEnv :: (TypeEnv -> TypeEnv) -> CheckEnv -> CheckEnv
modifyEnv f env = env { typeEnv = f (typeEnv env) }

assignType :: Ident -> Type -> CheckEnv -> CheckEnv
assignType ident t = modifyEnv (Map.insert ident t)

assignTypes :: [(Ident, Type)] -> CheckEnv -> CheckEnv
assignTypes = flip $ foldr (uncurry assignType)

-- getArgType :: ArgC -> Type
-- getArgType (Arg _ t _) = t

type Exc = Exc' BNFC'Position
data Exc' a
    = UnknownIdentifier !a !Ident
    | InvalidReturn !a
    | InvalidBreak !a
    | InvalidContinue !a
    | NotAFunction !a
    | TypeMismatch String !a !Type !Type
    | WrongNumberOfArguments !a
    | TCNotImplemented !a !String
    | NotAnLValue !a
    | RepeatedSDeclaration !a
    | NoEntryPoint !a
    | InvalidMain !a
    | DuplicatedParameterNames !a
    | NoReturn !a
    | RedeclarationOfBuiltIn !Ident !a
    | NoSuchAttribute !a !Ident
    deriving (Typeable)

instance {-# OVERLAPPING #-} Show BNFC'Position where
    show BNFC'NoPosition = ""
    show (BNFC'Position l c) = "(Line " ++ show l ++ ", column " ++ show c ++ ")"
    show _ = ""

instance {-# OVERLAPPING #-} Show Type where
    show :: Type -> String
    show (TInt _) = "int"
    show (TStr _) = "string"
    show (TBool _) = "bool"
    show (TVoid _) = "void"
    show (TArr _ t) = show t ++ "[]"
    show (TFun _ retType argTypes) = show retType ++ "(" ++ show argTypes ++ ")"
    show (TCls _ ident) = show ident

instance Show Exc where
    show (UnknownIdentifier pos ident) = "Unknown identifier " ++ show ident ++ " at " ++ show pos
    show (InvalidReturn pos) = "Invalid return at " ++ show pos
    show (InvalidBreak pos) = "Invalid break at " ++ show pos
    show (InvalidContinue pos) = "Invalid continue at " ++ show pos
    show (NotAFunction pos) = "Not a function at " ++ show pos
    show (TypeMismatch msg pos actual expected) = msg ++ " Type mismatch at " ++ show pos ++ ": " ++ "expected " ++ show expected ++ ", got " ++ show actual
    show (WrongNumberOfArguments pos) = "Wrong number of arguments at " ++ show pos
    show (TCNotImplemented pos msg) = "Not implemented at " ++ show pos ++ ": " ++ msg
    show (NotAnLValue pos) = "Not an lvalue at " ++ show pos
    show (RepeatedSDeclaration pos) = "Repeated declaration at " ++ show pos
    show (NoEntryPoint pos) = "No entry point at " ++ show pos
    show (InvalidMain pos) = "Invalid main at " ++ show pos
    show (DuplicatedParameterNames pos) = "Duplicated parameter names at " ++ show pos
    show (NoReturn pos) = "No return in function returning non-void at " ++ show pos
    show (RedeclarationOfBuiltIn (Ident ident) pos) = "Redeclaration of built-in function " ++ show ident ++ " at " ++ show pos
    show (NoSuchAttribute pos ident) = "No such attribute " ++ show ident ++ " at " ++ show pos

instance Exception Exc

type IM = ReaderT CheckEnv (ExceptT Exc Identity)

evalMaybe :: Exc -> Maybe a -> IM a
evalMaybe e Nothing = throwError e
evalMaybe _ (Just a) = pure a

getType :: BNFC'Position -> Ident -> IM Type
getType pos ident@(Ident i) = do
    env <- ask
    case Map.lookup ident (typeEnv env) of
        Just t -> return t
        Nothing -> do
            case clsName env of
                Just clsname -> getMember clsname ident
                Nothing -> throwError $ UnknownIdentifier pos (Ident $ i ++ "gettype")

class Inspectable a where
    inspect :: a -> IM Type

instance Inspectable Expr where
    inspect (ELitNull pos) = return $ TCls pos (Ident "null")
    inspect (ELitInt pos _) = return $ TInt pos
    inspect (EString pos _) = return $ TStr pos
    inspect (ELitTrue pos) = return $ TBool pos
    inspect (ELitFalse pos) = return $ TBool pos
    inspect (ERel pos lhs _ rhs) = return $ TBool pos
    inspect (ELVal pos (LVar _ ident)) = getType pos ident
    inspect (ELVal pos (LArrAcc _ expr_arr expr_ind)) = do
        check expr_arr
        t <- inspect expr_arr
        check expr_ind
        t' <- inspect expr_ind
        case t' of
            TInt _ -> case t of
                TArr _ t'' -> return t''
                _ -> throwError $ TypeMismatch "Not an array!" pos t (TArr BNFC'NoPosition t')
            _ -> throwError $ TypeMismatch "Index not an int!" pos t' t
    inspect (ELVal pos (LAttrAcc _ expr ident)) = do
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                getMember clsname ident
            TArr _ _ -> if ident == Ident "length" then return $ TInt pos else throwError $ TypeMismatch "Arrays have no attributes" pos t (TCls BNFC'NoPosition ident)
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)
    inspect (EAdd pos lhs _ rhs) = inspect lhs
    inspect (EMul pos lhs _ rhs) = return $ TInt pos
    inspect (ENeg pos expr) = return $ TInt pos
    inspect (EApp pos ident exprs) = do
        env <- ask
        let currentCls = clsName env
        case currentCls of
            Just clsIdent -> do
                member <- tryGetMember clsIdent ident
                case member of
                    Just (TFun pos2 retType argTypes) -> do
                        return retType
                    Nothing -> do
                        t <- getType pos ident
                        case t of
                            TFun pos2 retType argTypes -> do
                                return retType
                            _ -> throwError $ NotAFunction pos
            Nothing -> do
                t <- getType pos ident
                case t of
                    TFun pos2 retType argTypes -> do
                        return retType
                    _ -> throwError $ NotAFunction pos
    -- inspect (EApp pos ident args) = do
    --     env <- ask
    --     let currentCls = clsName env
    --     case currentCls of
    --         (Just )
    --     memb <- tryGetMember
    --     t <- getType pos ident
    --     case t of
    --         TFun _ retType argTypes -> return retType
    --         _ -> throwError $ NotAFunction pos
    inspect (EAnd pos lhs _ rhs) = return $ TBool pos
    inspect (EOr pos lhs _ rhs) = return $ TBool pos
    inspect (ENot pos expr) = return $ TBool pos
    inspect (ENewArr pos t expr) = return $ TArr pos t
    inspect (ENew pos ident) = return $ TCls pos ident
    inspect (EMethodApply pos expr ident@(Ident i) args) = do
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                memb <- tryGetMember clsname ident
                case memb of
                    Just (TFun pos2 retType argTypes) -> do
                        ret <- checkFunctionApplication pos retType argTypes args
                        return retType
                    Just _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)
                    Nothing -> throwError $ NoSuchAttribute pos ident
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)
    inspect (ECast pos type_ _) = do
        return type_

instance Inspectable ArgC where
    inspect (Arg _ t _) = return t

instance Inspectable FunDefC where
    inspect (FunDef pos retType ident args block) = do
        args' <- mapM inspect args
        return $ TFun pos retType args'

notImplemented :: (Show a) => a -> IM b
notImplemented x = throwError $ TCNotImplemented BNFC'NoPosition $ show x

instance {-# OVERLAPPING #-} Eq Type where
    TInt _ == TInt _ = True
    TStr _ == TStr _ = True
    TBool _ == TBool _ = True
    TVoid _ == TVoid _ = True
    TFun _ retType1 argTypes1 == TFun _ retType2 argTypes2 = retType1 == retType2 && argTypes1 == argTypes2
    TArr _ t1 == TArr _ t2 = t1 == t2 -- todo: this is incorrect
    TCls _ ident1 == TCls _ ident2 = ident1 == ident2
    _ == _ = False

instance {-# OVERLAPPING #-} Eq ArgC where
    (==) :: ArgC -> ArgC -> Bool
    Arg _ t1 _ == Arg _ t2 _ = t1 == t2

class Checkable a where
    check :: a -> IM CheckEnv

filterFuns :: [TopDefC] -> [FunDefC]
filterFuns = foldr f [] where
    f :: TopDefC -> [FunDefC] -> [FunDefC]
    f (FunDefTop _ fundef) acc = fundef : acc
    f _ acc = acc

filterClasses :: [TopDefC] -> [ClsDefC]
filterClasses = foldr f [] where
    f :: TopDefC -> [ClsDefC] -> [ClsDefC]
    f (ClsDefTop _ clsdef) acc = clsdef : acc
    f _ acc = acc

getArgType :: ArgC -> Type
getArgType (Arg _ t _) = t

getMemberType :: ClsMemDeclC -> [(Ident, Type)]
getMemberType (ClsMthdDecl _ (FunDef _ retType ident args _)) = [(ident, TFun BNFC'NoPosition retType (map getArgType args))]
getMemberType (ClsAttrDecl _ t items) = map (\(AttrItem _ ident) -> (ident, t)) items

assignClass :: (Ident, Maybe Ident, TypeEnv) -> CheckEnv -> CheckEnv
assignClass (ident, identExt, classEnv) env = env { classes = Map.insert ident (identExt, classEnv) (classes env) }

getMemberTypes :: [ClsMemDeclC] -> [(Ident, Type)]
getMemberTypes = concatMap getMemberType

classEnvCyclic :: CheckEnv -> IM Bool
classEnvCyclic env = do
    let classes' = classes env
    let classIdents = Map.keys classes'
    or <$> mapM (inheritanceCyclic []) classIdents

    where
        inheritanceCyclic :: [Ident] -> Ident -> IM Bool
        inheritanceCyclic visited ident = do
            if ident `elem` visited then return True
            else case Map.lookup ident (classes env) of
                Just (Just identExt, _) -> inheritanceCyclic (ident : visited) identExt
                Just (Nothing, _) -> return False
                Nothing -> return True

classEnvContainsDuplicates :: ProgramC -> IM Bool
classEnvContainsDuplicates (Program _ topDefs) = do
    or <$> mapM f topDefs
    where
        f :: TopDefC -> IM Bool
        f (ClsDefTop _ (ClsDef _ ident clsMembers)) = doesClassContainDuplicatedDefs clsMembers
        f (ClsDefTop _ (ClsDefExt _ ident identExt clsMembers)) = doesClassContainDuplicatedDefs clsMembers
        f _ = return False

getDeclarations :: ProgramC -> CheckEnv
getDeclarations (Program _ topDefs) = foldr f initEnv topDefs where
    f :: TopDefC -> CheckEnv -> CheckEnv
    f (FunDefTop pos (FunDef _ retType ident args _)) env = assignType ident (TFun pos retType (map getArgType args)) env
    f (ClsDefTop _ (ClsDef _ ident clsMembers)) env = assignClass (ident, Nothing, Map.fromList $ getMemberTypes clsMembers) env
    f (ClsDefTop _ (ClsDefExt _ ident identExt clsMembers)) env = assignClass (ident, Just identExt, Map.fromList $ getMemberTypes clsMembers) env

instance Checkable ProgramC where
    check p@(Program _ topDefs) = do
        env <- ask
        -- check for redefined functions        
        let funs = filterFuns topDefs
        let funNamesPositions = map (\(FunDef pos _ ident _ _) -> (ident, pos)) funs
        -- add symbols already defined in env to funNamesPositiosn
        -- let envNames = Map.keys $ typeEnv env

        foldM_ (\localNames namePosition -> do
            let (name, pos) = namePosition
            if name `elem` [Ident "printString", Ident "printInt", Ident "readString", Ident "readInt", Ident "error"] then
                throwError $ RedeclarationOfBuiltIn name pos
            else
                if Data.member name localNames then
                    throwError $ RepeatedSDeclaration pos
                else
                    return $ Data.insert name localNames
            ) (Data.empty :: Data.Set Ident) funNamesPositions

        let env' = getDeclarations (Program BNFC'NoPosition topDefs)

        duplicates <- classEnvContainsDuplicates p
        if duplicates then
            throwError $ TCNotImplemented BNFC'NoPosition "Duplicated class members"
        else do
            cyclic <- classEnvCyclic env'
            if cyclic then
                throwError $ TCNotImplemented BNFC'NoPosition "Cyclic inheritance"
            else do
                foldM_ (\env' topDef -> local (const env') (check topDef)) env' topDefs
                -- ensure no __internal_concat function is defined
                case Map.lookup (Ident "__internal_concat") (typeEnv env') of
                    Just (TFun pos _ _) -> throwError $ RedeclarationOfBuiltIn (Ident "__internal_concat") pos
                    _ -> return env'

                -- check main type
                case Map.lookup (Ident "main") (typeEnv env') of
                    Nothing -> throwError $ NoEntryPoint BNFC'NoPosition
                    Just (TFun pos retType args) -> do
                        Control.Monad.when (retType /= TInt BNFC'NoPosition) $ throwError $ TypeMismatch "Main has to return int!" BNFC'NoPosition retType (TInt BNFC'NoPosition)
                        Control.Monad.when (args /= []) $ throwError $ InvalidMain pos
                        return env'
                    _ -> throwError $ UnknownIdentifier BNFC'NoPosition (Ident "main")

instance Checkable BlockC where
    check (Block _ stmts) = do
        -- check if names in declarations are unique
        -- if any is not unique, print its position
        let decls = filter (\case { SDecl {} -> True ; _ -> False }) stmts
        let declNamesPositions = concatMap (\(SDecl _ _ items) -> map (\case { DeclNoInit pos ident -> (ident, pos) ; DeclInit pos ident _ -> (ident, pos) }) items) decls

        foldM_ (\localNames namePosition -> do
            let (name, pos) = namePosition
            if Data.member name localNames then
                throwError $ RepeatedSDeclaration pos
            else
                return $ Data.insert name localNames
            ) (Data.empty :: Data.Set Ident) declNamesPositions
        env <- ask
        foldM (\env' stmt -> local (const env') (check stmt)) env stmts

-- function to check if block of statements contains return statement
hasReturn :: BlockC -> Bool
hasReturn (Block _ stmts) = any isReturn stmts
    where
        isReturn :: Stmt -> Bool
        isReturn (SRetVoid _) = True
        isReturn (SRetExp _ _) = True
        isReturn (SCondElse _ (ELitTrue _) stmt _) = isReturn stmt
        isReturn (SCondElse _ (ELitFalse _) _ stmt) = isReturn stmt
        isReturn (SCondElse _ _ stmt1 stmt2) = isReturn stmt1 && isReturn stmt2
        isReturn (SCond _ (ELitTrue _) stmt) = isReturn stmt
        isReturn (SCond _ _ stmt) = False
        isReturn (SBlock _ block) = hasReturn block
        isReturn (SWhile _ (ELitTrue _) stmt) = isReturn stmt
        isReturn (SFor _ _ _ _ stmt) = False
        isReturn _ = False

fieldDefinedInSuperClass :: Ident -> Ident -> IM Bool
fieldDefinedInSuperClass clsname field = do
    env <- ask
    let classes' = classes env
    case Map.lookup clsname classes' of
        Just (Just identExt, classEnv) -> do
            case Map.lookup field classEnv of
                Just _ -> return True
                Nothing -> fieldDefinedInSuperClass identExt field
        Just (Nothing, classEnv) -> case Map.lookup field classEnv of
            Just _ -> return True
            Nothing -> return False
        Nothing -> return False

getMemberNames :: ClsMemDeclC -> [Ident]
getMemberNames (ClsMthdDecl _ (FunDef _ _ ident _ _)) = [ident]
getMemberNames (ClsAttrDecl _ _ items) = map (\(AttrItem _ ident) -> ident) items

doesClassContainDuplicatedDefs :: [ClsMemDeclC] -> IM Bool
doesClassContainDuplicatedDefs members = do
    let memberNames = concatMap getMemberNames members
    return $ nub memberNames /= memberNames

getParent :: Ident -> IM (Maybe Ident)
getParent ident = do
    env <- ask
    case Map.lookup ident (classes env) of
        Just (identExt, _) -> return identExt
        Nothing -> return Nothing

isTypeVoid :: Type -> Bool
isTypeVoid (TVoid _) = True
isTypeVoid (TArr _ t) = isTypeVoid t
isTypeVoid _ = False

ensureClassesExist :: Type -> IM ()
ensureClassesExist (TCls pos ident) = do
    env <- ask
    case Map.lookup ident (classes env) of
        Just _ -> return ()
        Nothing -> throwError $ UnknownIdentifier pos ident
ensureClassesExist (TArr pos t) = ensureClassesExist t
ensureClassesExist _ = return ()

instance Checkable ClsMemDeclC where
    check (ClsMthdDecl _ fun) = check fun

    check (ClsAttrDecl _ t items) = do
        env <- ask
        if isTypeVoid t then throwError $ TypeMismatch "Cannot declare void type!" BNFC'NoPosition t (TVoid BNFC'NoPosition)
        else do
            case clsName env of
                Just clsname -> do
                    supercls <- getParent clsname
                    case supercls of
                        Just supercls' -> do
                            mapM_ (\(AttrItem pos ident) -> do
                                fieldDefinedInSuperClass supercls' ident >>= \case
                                    True -> throwError $ DuplicatedParameterNames pos
                                    False -> return ()
                                ) items
                        Nothing -> return ()
                Nothing -> throwError $ TCNotImplemented BNFC'NoPosition "Class attribute outside class"

            ensureClassesExist t
            attrNames <- mapM (\(AttrItem _ ident) -> return ident) items
            Control.Monad.when (nub attrNames /= attrNames) $ throwError $ DuplicatedParameterNames BNFC'NoPosition

            let env' = assignTypes (map (\(AttrItem _ ident) -> (ident, t)) items) env
            return env'

instance Checkable FunDefC where
    check (FunDef pos retType ident args block) = do
        env <- ask
        -- if any argument has void type or class-type which doesn't exist, reject
        foldM_ (\_ (Arg _ t _) -> case t of
            TCls _ ident -> do
                env <- ask
                case Map.lookup ident (classes env) of
                    Just _ -> return ()
                    Nothing -> throwError $ UnknownIdentifier pos ident
            TArr _ t' -> case t' of
                TCls _ ident -> do
                    env <- ask
                    case Map.lookup ident (classes env) of
                        Just _ -> return ()
                        Nothing -> throwError $ UnknownIdentifier pos ident
                TVoid _ -> throwError $ TypeMismatch "Argument cannot have void type!" pos t (TVoid BNFC'NoPosition)
                _ -> return ()
            TVoid _ -> throwError $ TypeMismatch "Argument cannot have void type!" pos t (TVoid BNFC'NoPosition)
            _ -> return ()) () args

        argNames <- mapM (\(Arg _ _ ident) -> return ident) args
        Control.Monad.when (nub argNames /= argNames) $ throwError $ DuplicatedParameterNames pos
        let funType = TFun pos retType (map (\(Arg _ t _) -> t) args)
        let env' = assignType ident funType env
        local (const $ bindArgs args $ env' {retType = Just retType}) (check block)

        case retType of
            TVoid _ -> return env'
            _ -> if hasReturn block then return env' else throwError $ NoReturn pos

        where
            getArgType :: ArgC -> Type
            getArgType (Arg _ t _) = t

            bindArgs :: [ArgC] -> CheckEnv -> CheckEnv
            bindArgs args = assignTypes $ map (\arg -> (getIdent arg, getArgType arg)) args

            getIdent :: ArgC -> Ident
            getIdent (Arg _ _ ident) = ident

defineClass :: BNFC'Position -> Ident -> Maybe Ident -> [ClsMemDeclC] -> IM CheckEnv
defineClass pos ident identExt clsMembers = do
    envRaw' <- ask
    let envRaw = envRaw' { clsName = Just ident }
    let env' = envRaw { typeEnv = Map.insert (Ident "self") (TCls BNFC'NoPosition ident) (typeEnv envRaw) }

    -- check the members
    mapM_ (local (const env') . check) clsMembers
    ask

instance Checkable TopDefC where
    check (FunDefTop _ fun) = check fun
    check (ClsDefTop pos (ClsDef _ ident clsMembers)) = defineClass pos ident Nothing clsMembers
    check (ClsDefTop pos (ClsDefExt _ ident identExt clsMembers)) = do
        if ident == identExt then throwError $ TypeMismatch "Circular inheritance" pos (TCls pos ident) (TCls pos identExt)
        else defineClass pos ident (Just identExt) clsMembers

instance Checkable LVal where
    check (LVar pos ident) = do
        env <- ask
        getType pos ident
        -- evalMaybe (UnknownIdentifier pos ident) (Map.lookup ident (typeEnv env))
        return env
    check (LArrAcc pos exprarr expr) = do
        check exprarr
        check expr
        env <- ask
        t <- inspect exprarr
        case t of
            TArr _ _ -> do
                t' <- inspect expr
                case t' of
                    TInt _ -> return env
                    _ -> throwError $ TypeMismatch "Index not an int!" pos t' t
            _ -> throwError $ TypeMismatch "Not an array!" pos t (TArr BNFC'NoPosition t)
    check (LAttrAcc pos expr ident) = do
        env <- ask
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                mem <- getMember clsname ident
                return env
                -- let classes' = classes env
                -- case Map.lookup clsname classes' of
                --     Just (baseCls, classEnv) -> do
                --         case Map.lookup ident classEnv of
                --             Just t -> return env
                --             Nothing -> throwError $ NoSuchAttribute pos ident
                --     Nothing -> throwError $ UnknownIdentifier pos ident
            TArr _ _ -> if ident == Ident "length" then return env else throwError $ TypeMismatch "Arrays have no attributes" pos t (TCls BNFC'NoPosition ident)
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)

isInstance :: Type -> Type -> IM Bool
isInstance (TCls _ (Ident "null")) (TCls {}) = return True
isInstance (TCls _ (Ident "null")) (TArr {}) = return True
isInstance (TCls _ ident1) (TCls _ ident2) = do
    if ident1 == ident2 then return True else do
        env <- ask
        let classes' = classes env
        case Map.lookup ident1 classes' of
            Just (Just identExt, _) -> isInstance (TCls BNFC'NoPosition identExt) (TCls BNFC'NoPosition ident2)
            Just (_, classEnv) -> return False
            Nothing -> return False
isInstance t1 t2 = return $ t1 == t2

isArrayLength :: LVal -> IM Bool
isArrayLength (LAttrAcc _ expr (Ident "length")) = do
    t <- inspect expr
    case t of
        TArr _ _ -> return True
        _ -> return False
isArrayLength _ = return False

instance Checkable Stmt where
    check (SFor pos t ident expr stmt) = do
        env <- ask
        check expr
        t' <- inspect expr
        case t' of
            TArr _ t'' -> do
                isInst <- isInstance t'' t
                if isInst then do
                    let env' = assignType ident t env
                    local (const env') (check stmt)
                    ask
                else throwError $ TypeMismatch "Array element type doesn't match loop variable type!" pos t t''
            _ -> throwError $ TypeMismatch "Not an array!" pos t' (TArr BNFC'NoPosition t')
    check (SEmpty _) = ask
    check (SBlock _ block) = do
        env <- ask
        local (const env {inLoop = False}) (check block)
    check (SExp _ expr) = do
        check expr
        ask
    
    check (SIncr pos lval) = do
        isA <- isArrayLength lval
        if isA then throwError $ TypeMismatch "Cannot increment array length!" pos (TArr BNFC'NoPosition (TInt BNFC'NoPosition)) (TInt BNFC'NoPosition)
        else do
            check lval
            t <- inspect (ELVal pos lval)
            case t of
                TInt _ -> ask
                _ -> throwError $ TypeMismatch "Not an int!" pos t (TInt BNFC'NoPosition)
    check (SDecr pos lval) = do
        isA <- isArrayLength lval
        if isA then throwError $ TypeMismatch "Cannot decrement array length!" pos (TArr BNFC'NoPosition (TInt BNFC'NoPosition)) (TInt BNFC'NoPosition)
        else do
            check lval
            t <- inspect (ELVal pos lval)
            case t of
                TInt _ -> ask
                _ -> throwError $ TypeMismatch "Not an int!" pos t (TInt BNFC'NoPosition)
    check (SRetVoid pos) = do
        env <- ask
        case retType env of
            Nothing -> throwError $ InvalidReturn pos
            Just (TVoid _) -> ask
            Just t -> throwError $ TypeMismatch "Void return in non-void function!" pos t (TVoid BNFC'NoPosition)
    check (SRetExp pos expr) = do
        env <- ask
        case retType env of
            Nothing -> throwError $ InvalidReturn pos
            Just t -> do
                check expr
                t' <- inspect expr
                isInst <- isInstance t' t
                if isInst then return env else throwError $ TypeMismatch "Function return type doesn't match!" pos t t'

    check (SDecl pos (TVoid _) items) = do
        throwError $ TypeMismatch "Cannot declare a void variable!" pos (TVoid BNFC'NoPosition) (TVoid BNFC'NoPosition)
    
    check (SDecl pos (TArr _ (TVoid _)) items) = do
        throwError $ TypeMismatch "Cannot declare an array of voids!" pos (TArr BNFC'NoPosition (TVoid BNFC'NoPosition)) (TArr BNFC'NoPosition (TVoid BNFC'NoPosition))
    
    check (SDecl pos t items) = do
        env <- ask
        ensureClassesExist t
        foldM (\env' item -> local (const env') (check_item item)) env items

        where
        check_item (DeclInit pos ident expr) = do
            env <- ask
            check expr
            t' <- inspect expr
            isInst <- isInstance t' t
            if isInst then return $ assignType ident t env else throwError $ TypeMismatch "Right-hand side type doesn't match declaration type!" pos t t'

        check_item (DeclNoInit _ ident) = asks $ assignType ident t

    check (SCondElse pos expr stmt1 stmt2) = do
        env <- ask
        check expr
        t <- inspect expr
        case t of
            TBool _ -> do
                check stmt1
                check stmt2
                ask
            _ -> throwError $ TypeMismatch "Not a bool!" pos t (TBool BNFC'NoPosition)
    check (SCond pos expr stmt) = do
        env <- ask
        check expr
        t <- inspect expr
        case t of
            TBool _ -> do
                check stmt
                ask
            _ -> throwError $ TypeMismatch "Not a bool!" pos t (TBool BNFC'NoPosition)
    
    check (SAss pos (LVar _ (Ident "self")) _) = throwError $ TypeMismatch "Cannot assign to self!" pos (TCls BNFC'NoPosition (Ident "self")) (TCls BNFC'NoPosition (Ident "self"))
    check (SAss pos lv@(LVar pos2 ident) (ELitNull _)) = do
        check lv
        t <- getType pos2 ident
        case t of
            TCls _ _ -> ask
            TArr _ _ -> ask
            _ -> throwError $ TypeMismatch "Invalid null assignment" pos t (TCls BNFC'NoPosition (Ident "null"))
    check (SAss pos lv@(LVar pos2 ident) expr) = do
        check lv
        t1 <- getType pos2 ident
        check expr
        t2 <- inspect expr
        isInst <- isInstance t2 t1
        if isInst then ask else throwError $ TypeMismatch "Right-hand side type doesn't match assignment target type!" pos t1 t2

    check (SAss pos lv@(LArrAcc pos2 expr_arr expr_ind) expr) = do
        check lv
        check expr_arr
        t1 <- inspect expr_arr
        check expr_ind
        t2 <- inspect expr_ind
        case t2 of
            TInt _ -> do
                check expr
                t3 <- inspect expr
                case t1 of
                    TArr _ arr_elem_type -> do
                        isInst <- isInstance t3 arr_elem_type
                        if isInst then ask else throwError $ TypeMismatch "RHS value type doesn't match array element type!" pos t1 t3
                    _ -> throwError $ TypeMismatch "RHS value type doesn't match array element type!" pos t1 t3
            _ -> throwError $ TypeMismatch "Index not an int!" pos t2 t1
    
    check (SAss pos lv@(LAttrAcc _ expr ident) expr_assigned) = do
        check lv
        t1 <- inspect expr
        check expr_assigned
        t2 <- inspect expr_assigned
        case t1 of
            TArr _ _ -> throwError $ TypeMismatch "Arrays have no attributes" pos t1 (TCls BNFC'NoPosition ident)
            TCls _ clsname -> do
                memb <- getMember clsname ident
                case memb of
                    TFun pos2 retType argTypes -> throwError $ TypeMismatch "Cannot assign to a function!" pos t1 (TFun pos2 retType argTypes)
                    _ -> do
                        isInst <- isInstance t2 memb
                        if isInst then ask else throwError $ TypeMismatch "RHS value type doesn't match attribute type!" pos memb t2
            _ -> throwError $ TypeMismatch "Not a class!" pos t1 (TCls pos ident)

    check (SWhile pos expr block) = do
        check expr
        t <- inspect expr
        case t of
            -- this might be incorrect, as we return env at the end of block,
            -- but we should forget the declarations in it
            TBool _ -> do
                check block
                ask
            _ -> throwError $ TypeMismatch "Invalid while condition type" pos t (TBool BNFC'NoPosition)


checkFunctionApplication :: BNFC'Position -> Type -> [Type] -> [Expr] -> IM CheckEnv
checkFunctionApplication pos retType argTypes exprs = do
    Control.Monad.when (length exprs /= length argTypes) $ throwError $ WrongNumberOfArguments pos
    exprTypes <- mapM inspect exprs
    firstNotMatchingType <- firstNotMatching exprTypes argTypes
    case firstNotMatchingType of
        Nothing -> ask
        Just (actual, expected) -> throwError $ TypeMismatch "Invalid argument types" pos actual expected
    where
        firstNotMatching (x:xs) (y:ys) = do
            isInst <- isInstance x y
            if isInst then firstNotMatching xs ys else return $ Just (x, y)
        firstNotMatching _ _ = return Nothing

getBaseClass :: Ident -> IM Ident
getBaseClass ident = do
    env <- ask
    case Map.lookup ident (classes env) of
        Just (Just identExt, _) -> getBaseClass identExt
        Just (Nothing, _) -> return ident
        Nothing -> throwError $ UnknownIdentifier BNFC'NoPosition ident

instance Checkable Expr where
    check (EApp pos ident exprs) = do
        env <- ask
        let currentCls = clsName env
        case currentCls of
            Just clsIdent -> do
                member <- tryGetMember clsIdent ident
                case member of
                    Just (TFun pos2 retType argTypes) -> do
                        checkFunctionApplication pos retType argTypes exprs
                    Nothing -> do
                        t <- getType pos ident
                        case t of
                            TFun pos2 retType argTypes -> do
                                checkFunctionApplication pos retType argTypes exprs
                            _ -> throwError $ NotAFunction pos
            Nothing -> do
                t <- getType pos ident
                case t of
                    TFun pos2 retType argTypes -> do
                        checkFunctionApplication pos retType argTypes exprs
                    _ -> throwError $ NotAFunction pos

    check (ELVal pos (LVar _ ident)) = do
        getType pos ident
        ask

    check (ELVal pos (LArrAcc pos2 expr_arr expr)) = do
        check expr_arr
        t <- inspect expr_arr
        check expr
        t' <- inspect expr
        case t' of
            TInt _ -> case t of
                TArr _ t' -> ask
                _ -> throwError $ TypeMismatch "Not an array!" pos t (TArr BNFC'NoPosition t')
            _ -> throwError $ TypeMismatch "Invalid index type" pos t' (TInt BNFC'NoPosition)

    check (ELVal pos lv@(LAttrAcc pos2 expr ident)) = do
        check lv
        check expr
        t <- inspect expr
        case t of
            TCls _ ident -> ask
            TArr _ _ -> if ident == Ident "length" then ask else throwError $ TypeMismatch "Arrays have no attributes" pos t (TCls BNFC'NoPosition ident)
            _ -> throwError $ TypeMismatch "(todo) Invalid attribute access" pos t (TCls BNFC'NoPosition ident)

    check (ERel pos expr1 op expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2

        case (t1, t2) of
            (TCls _ (Ident "null"), TCls {}) -> throwIfBadOpElseAsk op t1 t2
            (TCls {}, TCls _ (Ident "null")) -> throwIfBadOpElseAsk op t1 t2
            (TArr {}, TCls _ (Ident "null")) -> throwIfBadOpElseAsk op t1 t2
            (TCls _ (Ident "null"), TArr {}) -> throwIfBadOpElseAsk op t1 t2
            (TCls _ clsname1, TCls _ clsname2) -> do
                base1 <- getBaseClass clsname1
                base2 <- getBaseClass clsname2
                if base1 == base2 then throwIfBadOpElseAsk op t1 t2
                else throwError $ TypeMismatch "Incomparable classes" pos t1 t2
            (TInt _, TInt _) -> ask
            (TStr _, TStr _) -> do
                case op of
                    OpEq _ -> ask
                    OpNe _ -> ask
                    _ -> throwError $ TypeMismatch "Unsupported operation for strings!" pos t1 t2
            (TBool _, TBool _) -> throwIfBadOpElseAsk op t1 t2
            (TArr _ (TCls _ clsname1), TArr _ (TCls _ clsname2)) -> do
                base1 <- getBaseClass clsname1
                base2 <- getBaseClass clsname2
                if base1 == base2 then throwIfBadOpElseAsk op t1 t2
                else throwError $ TypeMismatch "Incomparable classes" pos t1 t2
            (TArr _ t1, TArr _ t2) -> do
                if t1 == t2 then throwIfBadOpElseAsk op t1 t2
                else throwError $ TypeMismatch "Incomparable array types" pos t1 t2
            _ -> throwError $ TypeMismatch "Incomparable types!" pos t1 t2
        where
            throwIfBadOpElseAsk :: Op -> Type -> Type -> IM CheckEnv
            throwIfBadOpElseAsk op t1 t2 = do
                case op of
                    OpEq _ -> ask
                    OpNe _ -> ask
                    _ -> throwError $ TypeMismatch "Invalid operation for class types" pos t1 t2


    check (ENeg pos expr) = do
        check expr
        t <- inspect expr
        case t of
            TInt _ -> ask
            _ -> throwError $ TypeMismatch "Cannot negate a non-int type!" pos t (TInt BNFC'NoPosition)

    check (EAdd pos expr1 op expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            TInt _ -> case t2 of
                TInt _ -> ask
                _ -> throwError $ TypeMismatch "Cannot add non-int to an int!" pos t1 t2
            TStr _ -> case t2 of
                TStr _ ->
                    case op of
                        OpAdd _ -> ask
                        _ -> throwError $ TypeMismatch "Unsupported operation for strings!" pos t1 t2
                _ -> throwError $ TypeMismatch "Cannot concatenate non-string to a string!" pos t1 t2
            _ -> throwError $ TypeMismatch "+ operator only supported for ints and strings!" pos t1 t2
    
    -- todo: to sie pierdoli w tescie (false && (1 / 0))
    -- check (EMul pos _ (OpDiv _) (ELitInt _ 0)) = throwError $ TypeMismatch "todo: division by zero" pos (TInt BNFC'NoPosition) (TInt BNFC'NoPosition)
    -- check (EMul pos _ (OpMod _) (ELitInt _ 0)) = throwError $ TypeMismatch "todo: division by zero" pos (TInt BNFC'NoPosition) (TInt BNFC'NoPosition)
    check (EMul pos expr1 op expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            TInt _ -> case t2 of
                TInt _ -> ask
                _ -> throwError $ TypeMismatch "Cannot multiply an int by a non-int!" pos t1 t2
            _ -> throwError $ TypeMismatch "* operator only supported for ints!" pos t1 t2

    check (ELitInt pos int) = do
        -- detect 32 bit signed overflow
        if int > 2147483647 || int < -2147483648 then
            throwError $ TypeMismatch "todo: num too big" pos (TInt BNFC'NoPosition) (TInt BNFC'NoPosition)
        else ask
    check (EString _ _) = ask
    check (ELitTrue _) = ask
    check (ELitFalse _) = ask
    check (ENot pos expr) = do
        check expr
        t <- inspect expr
        case t of
            TBool _ -> ask
            _ -> throwError $ TypeMismatch "Not operator only supported for bools" pos t (TBool BNFC'NoPosition)
    check (EOr pos expr1 _ expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            TBool _ -> case t2 of
                TBool _ -> ask
                _ -> throwError $ TypeMismatch "| operator only supported for bools!" pos t1 t2
            _ -> throwError $ TypeMismatch "| operator only supported for bools!" pos t1 t2
    check (EAnd pos expr1 _ expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            TBool _ -> case t2 of
                TBool _ -> ask
                _ -> throwError $ TypeMismatch "& operator only supported for bools!" pos t1 t2
            _ -> throwError $ TypeMismatch "& operator only supported for bools!" pos t1 t2

    check (ENewArr pos t expr) = do
        case t of
            TCls _ ident -> do
                env <- ask
                classes' <- asks classes
                case Map.lookup ident classes' of
                    Just classEnv -> do
                        check expr
                        t' <- inspect expr
                        case t' of
                            TInt _ -> ask
                            _ -> throwError $ TypeMismatch "Array size not an int!" pos t' (TInt BNFC'NoPosition)
                    Nothing -> throwError $ UnknownIdentifier pos ident
            _ -> do
                check expr
                t' <- inspect expr
                case t' of
                    TInt _ -> ask
                    _ -> throwError $ TypeMismatch "Array size not an int!" pos t' (TInt BNFC'NoPosition)

    check (ENew pos ident) = do
        env <- ask
        case Map.lookup ident (classes env) of
            Just _ -> ask
            Nothing -> throwError $ UnknownIdentifier pos ident

    check (EMethodApply pos expr ident exprs) = do
        env <- ask
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                memb <- getMember clsname ident
                case memb of
                    TFun pos2 retType argTypes -> do
                        checkFunctionApplication pos retType argTypes exprs
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)

    check (ECast pos type_ toknull) = do
        case type_ of
            TCls _ ident -> do
                env <- ask
                classes' <- asks classes
                case Map.lookup ident classes' of
                    Just classEnv -> ask
                    Nothing -> throwError $ UnknownIdentifier pos ident
            TArr _ t -> ask
            _ -> throwError $ TypeMismatch "Cannot cast to non-class type!" pos type_ (TCls BNFC'NoPosition (Ident "unknown"))

    check (ELitNull pos) = ask

tryGetMember :: Ident -> Ident -> IM (Maybe Type)
tryGetMember clsname ident = do
    env <- ask
    let classes' = classes env
    case Map.lookup clsname classes' of
        Just (Just base, classEnv) -> do
            case Map.lookup ident classEnv of
                Just t -> return (Just t)
                Nothing -> tryGetMember base ident
        Just (_, classEnv) -> do
            case Map.lookup ident classEnv of
                Just t -> return (Just t)
                Nothing -> return Nothing
        _ -> return Nothing

getMember :: Ident -> Ident -> IM Type
getMember clsname ident = do
    env <- ask
    let classes' = classes env
    case Map.lookup clsname classes' of
        Just (Just base, classEnv) -> do
            case Map.lookup ident classEnv of
                Just t -> return t
                Nothing -> getMember base ident
        Just (_, classEnv) -> do
            case Map.lookup ident classEnv of
                Just t -> return t
                Nothing -> throwError $ NoSuchAttribute BNFC'NoPosition ident
        _ -> throwError $ UnknownIdentifier BNFC'NoPosition ident

initEnv = CheckEnv {
    typeEnv = Map.fromList [
        (Ident "printString", TFun BNFC'NoPosition (TVoid BNFC'NoPosition) [TStr BNFC'NoPosition]),
        (Ident "printInt", TFun BNFC'NoPosition (TVoid BNFC'NoPosition) [TInt BNFC'NoPosition]),
        (Ident "readInt", TFun BNFC'NoPosition (TInt BNFC'NoPosition) []),
        (Ident "readString", TFun BNFC'NoPosition (TStr BNFC'NoPosition) []),
        (Ident "error", TFun BNFC'NoPosition (TVoid BNFC'NoPosition) [])
    ],
    retType = Nothing,
    inLoop = False,
    classes = Map.empty,
    clsName = Nothing
}

typeCheck_ :: ProgramC -> Except Exc CheckEnv
typeCheck_ p = do
    case runIdentity $ runExceptT $ runReaderT (check p) initEnv of
        Left err -> throw err
        Right env -> return env


typeCheck :: ProgramC -> IO ()
typeCheck p = do
    case runIdentity $ runExceptT $ runReaderT (check p) initEnv of
        Left err -> do
            hPutStrLn stderr "ERROR"
            throw err
        Right env -> return ()