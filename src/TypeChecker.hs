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
    classes :: !(Map Ident (Maybe Ident, TypeEnv))
}

modifyEnv :: (TypeEnv -> TypeEnv) -> CheckEnv -> CheckEnv
modifyEnv f env = env { typeEnv = f (typeEnv env) }

assignType :: Ident -> Type -> CheckEnv -> CheckEnv
assignType ident t = modifyEnv (Map.insert ident t)

assignTypes :: [(Ident, Type)] -> CheckEnv -> CheckEnv
assignTypes = flip $ foldr (uncurry assignType)

getArgType :: ArgC -> Type
getArgType (Arg _ t _) = t

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
getType pos ident = do
    env <- ask
    evalMaybe (UnknownIdentifier pos ident) (Map.lookup ident (typeEnv env))

class Inspectable a where
    inspect :: a -> IM Type

instance Inspectable Expr where
    inspect (ELitInt pos _) = return $ TInt pos
    inspect (EString pos _) = return $ TStr pos
    inspect (ELitTrue pos) = return $ TBool pos
    inspect (ELitFalse pos) = return $ TBool pos
    inspect (ERel pos lhs _ rhs) = return $ TBool pos
    inspect (ELVal pos (LVar _ ident)) = getType pos ident
    inspect (ELVal pos (LArrAcc _ expr_arr expr_ind)) = notImplemented "array access"
    inspect (ELVal pos (LAttrAcc _ expr ident)) = notImplemented "attribute access"
    inspect (EAdd pos lhs _ rhs) = inspect lhs
    inspect (EMul pos lhs _ rhs) = return $ TInt pos
    inspect (ENeg pos expr) = return $ TInt pos
    inspect (EApp pos ident args) = do
        t <- getType pos ident
        case t of
            TFun _ retType argTypes -> return retType
            _ -> throwError $ NotAFunction pos
    inspect (EAnd pos lhs _ rhs) = return $ TBool pos
    inspect (EOr pos lhs _ rhs) = return $ TBool pos
    inspect (ENot pos expr) = return $ TBool pos
    inspect (ENewArr pos t expr) = return $ TArr pos t
    inspect (ENew pos ident) = return $ TCls pos ident
    inspect (EMethodApply pos expr ident args) = do
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                env <- ask
                let classes' = classes env
                case Map.lookup clsname classes' of
                    Just (baseCls, classEnv) -> do
                        case Map.lookup ident classEnv of
                            Just (TFun pos2 retType argTypes) -> return retType
                            Nothing -> throwError $ NoSuchAttribute pos ident
                    Nothing -> throwError $ UnknownIdentifier pos ident
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)
    inspect (ECast pos ident _) = do
        classes' <- asks classes
        case Map.lookup ident classes' of
            Just classEnv -> return $ TCls pos ident
            Nothing -> throwError $ UnknownIdentifier pos ident

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
    TArr _ t1 == TArr _ t2 = t1 == t2
    TCls _ ident1 == TCls _ ident2 = ident1 == ident2 -- todo: fix this for inheritance
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

getMemberType :: ClsMemDeclC -> [(Ident, Type)]
getMemberType (ClsMthdDecl _ (FunDef _ retType ident args _)) = [(ident, TFun BNFC'NoPosition retType (map getArgType args))]
getMemberType (ClsAttrDecl _ t items) = map (\(AttrItem _ ident) -> (ident, t)) items

getClassEnv :: ClsDefC -> (Ident, Maybe Ident, TypeEnv)
getClassEnv (ClsDef _ ident clsMembers) = (ident, Nothing, Map.fromList (concatMap getMemberType clsMembers))
getClassEnv (ClsDefExt _ ident identExt clsMembers) = (ident, Just identExt, Map.fromList (concatMap getMemberType clsMembers))

assignClasses :: [(Ident, Maybe Ident, TypeEnv)] -> CheckEnv -> CheckEnv
assignClasses = flip $ foldr (\(ident, identExt, classEnv) env -> env { classes = Map.insert ident (identExt, classEnv) (classes env) })

addFunctionDeclarations :: [TopDefC] -> CheckEnv -> CheckEnv
addFunctionDeclarations topDefs = assignTypes (map (\(FunDef pos retType ident args _) -> (ident, TFun pos retType (map (\(Arg _ t _) -> t) args))) (filterFuns topDefs))

addClassDeclarations :: [TopDefC] -> CheckEnv -> CheckEnv
addClassDeclarations topDefs = assignClasses (map getClassEnv (filterClasses topDefs))


instance Checkable ProgramC where
    -- take into account that function can be defined after it is used
    check (Program _ topDefs) = do
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

        let env'' = addFunctionDeclarations topDefs env
        let env' = assignClasses (map getClassEnv (filterClasses topDefs)) env''
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
        isReturn (SFor _ _ _ _ stmt) = isReturn stmt
        isReturn _ = False

instance Checkable ClsMemDeclC where
    check (ClsMthdDecl _ (FunDef _ retType ident args block)) = do
        env <- ask
        -- if any argument has void type, reject
        foldM_ (\_ (Arg _ t _) -> Control.Monad.when (t == TVoid BNFC'NoPosition) $ throwError $ TypeMismatch "Parameter cannot have void type!" BNFC'NoPosition t (TVoid BNFC'NoPosition)) () args

        argNames <- mapM (\(Arg _ _ ident) -> return ident) args
        Control.Monad.when (nub argNames /= argNames) $ throwError $ DuplicatedParameterNames BNFC'NoPosition
        let funType = TFun BNFC'NoPosition retType (map (\(Arg _ t _) -> t) args)
        let env' = assignType ident funType env
        -- set return type
        local (const env' {retType = Just retType}) (check block)

        case retType of
            TVoid _ -> return env'
            _ -> if hasReturn block then return env' else throwError $ NoReturn BNFC'NoPosition

    check (ClsAttrDecl _ t items) = do
        env <- ask
        -- if any argument has void type, reject
        Control.Monad.when (t == TVoid BNFC'NoPosition) $ throwError $ TypeMismatch "Attribute cannot have void type!" BNFC'NoPosition t (TVoid BNFC'NoPosition)

        attrNames <- mapM (\(AttrItem _ ident) -> return ident) items
        Control.Monad.when (nub attrNames /= attrNames) $ throwError $ DuplicatedParameterNames BNFC'NoPosition
        let env' = assignTypes (map (\(AttrItem _ ident) -> (ident, t)) items) env
        return env'

instance Checkable TopDefC where
    check (FunDefTop _ (FunDef pos retType ident args block)) = do
        env <- ask
        -- if any argument has void type, reject
        foldM_ (\_ (Arg _ t _) -> Control.Monad.when (t == TVoid BNFC'NoPosition) $ throwError $ TypeMismatch "Parameter cannot have void type!" pos t (TVoid BNFC'NoPosition)) () args

        argNames <- mapM (\(Arg _ _ ident) -> return ident) args
        Control.Monad.when (nub argNames /= argNames) $ throwError $ DuplicatedParameterNames pos
        let funType = TFun pos retType (map (\(Arg _ t _) -> t) args)
        let env' = assignType ident funType env
        local (const $ bindArgs args $ env' {retType = Just retType}) (check block)

        case retType of
            TVoid _ -> return env'
            _ -> if hasReturn block then return env' else throwError $ NoReturn pos

        where
            bindArgs :: [ArgC] -> CheckEnv -> CheckEnv
            bindArgs args = assignTypes $ map (\arg -> (getIdent arg, getArgType arg)) args
            getIdent :: ArgC -> Ident
            getIdent (Arg _ _ ident) = ident

    -- unverified
    check (ClsDefTop pos (ClsDef _ ident clsMembers)) = do
        env <- ask
        -- if class exists in the environment, reject
        -- Control.Monad.when (Map.member ident (typeEnv env)) $ throwError $ RepeatedSDeclaration pos
        -- Control.Monad.when (Map.member ident (classes env)) $ throwError $ RepeatedSDeclaration pos
        -- let env' = assignType ident (TCls pos ident) env
        -- let env' = assignTypes (map (\(FunDef pos retType ident args _) -> (ident, TFun pos retType (map (\(Arg _ t _) -> t) args))) (filterFuns topDefs)) env
        -- let env'' = foldM (\env' clsMember -> local (const env') (check clsMember)) env' clsMembers
        foldM (\env' clsMember -> local (const env') (check clsMember)) env clsMembers

    -- unverified
    check (ClsDefTop pos (ClsDefExt _ ident identExt clsMembers)) = do
        env <- ask
        -- if class exists in the environment, reject
        -- Control.Monad.when (Map.member ident (typeEnv env)) $ throwError $ RepeatedSDeclaration pos
        let env' = assignType ident (TCls pos identExt) env
        foldM (\env' clsMember -> local (const env') (check clsMember)) env' clsMembers

instance Checkable LVal where
    check (LVar pos ident) = do
        env <- ask
        evalMaybe (UnknownIdentifier pos ident) (Map.lookup ident (typeEnv env))
        return env
    check (LArrAcc pos exprarr expr) = do
        check exprarr
        check expr
    check (LAttrAcc pos expr ident) = do
        env <- ask
        check expr
        return env

instance Checkable Stmt where
    check (SEmpty _) = ask
    check (SBlock _ block) = do
        env <- ask
        local (const env {inLoop = False}) (check block)
    check (SExp _ expr) = do
        check expr
        ask
    check (SIncr pos lval) = do
        check lval
        t <- inspect (ELVal pos lval)
        case t of
            TInt _ -> ask
            _ -> throwError $ TypeMismatch "Not an int!" pos t (TInt BNFC'NoPosition)
    check (SDecr pos lval) = do
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
                if t == t' then return env else throwError $ TypeMismatch "Function return type doesn't match!" pos t t'

    check (SDecl pos (TVoid _) items) = do
        throwError $ TypeMismatch "Cannot declare a void variable!" pos (TVoid BNFC'NoPosition) (TVoid BNFC'NoPosition)

    check (SDecl pos t items) = do
        env <- ask
        foldM (\env' item -> local (const env') (check_item item)) env items

        where
        check_item (DeclInit pos ident expr) = do
            env <- ask
            check expr
            t' <- inspect expr
            if t == t' then return $ assignType ident t env else throwError $ TypeMismatch "Right-hand side type doesn't match declaration type!" pos t t'

        check_item (DeclNoInit _ ident) = asks $ assignType ident t

    check (SCondElse pos expr stmt1 stmt2) = do
        check expr
        t <- inspect expr
        case t of
            TBool _ -> do
                check stmt1
                check stmt2
            _ -> throwError $ TypeMismatch "Not a bool!" pos t (TBool BNFC'NoPosition)
    check (SCond pos expr stmt) = do
                check expr
                t <- inspect expr
                case t of
                    TBool _ -> check stmt
                    _ -> throwError $ TypeMismatch "Not a bool!" pos t (TBool BNFC'NoPosition)
    check (SAss pos (LVar pos2 ident) expr) = do
        t1 <- getType pos2 ident
        check expr
        t2 <- inspect expr
        if t1 == t2 then ask else throwError $ TypeMismatch "Right-hand side type doesn't match assignment target type!" pos t1 t2

    check (SAss pos (LArrAcc pos2 expr_arr expr_ind) expr) = do
        check expr_arr
        t1 <- inspect expr_arr
        check expr_ind
        t2 <- inspect expr_ind
        case t2 of
            TInt _ -> do
                check expr
                t3 <- inspect expr
                case t1 of
                    TArr _ t3 -> ask
                    _ -> throwError $ TypeMismatch "RHS value type doesn't match array element type!" pos t1 t3
            _ -> throwError $ TypeMismatch "Index not an int!" pos t2 t1

    check (SAss pos (LAttrAcc _ expr ident) expr_assigned) = do
        t1 <- inspect expr
        check expr_assigned
        t2 <- inspect expr_assigned
        case t1 of
            TArr _ _ -> throwError $ TypeMismatch "Arrays have no attributes" pos t1 (TCls BNFC'NoPosition ident)
            _ -> throwError $ TypeMismatch "Invalid attribute access" pos t1 (TCls BNFC'NoPosition ident)

    check (SWhile pos expr block) = do
        check expr
        t <- inspect expr
        case t of
            TBool _ -> check block
            _ -> throwError $ TypeMismatch "Invalid while condition type" pos t (TBool BNFC'NoPosition)
    check e = notImplemented e

checkFunctionApplication :: BNFC'Position -> Type -> [Type] -> [Expr] -> IM CheckEnv
checkFunctionApplication pos retType argTypes exprs = do
    Control.Monad.when (length exprs /= length argTypes) $ throwError $ WrongNumberOfArguments pos
    exprTypes <- mapM inspect exprs
    if exprTypes /= argTypes then
        let foo = firstNotMatching exprTypes argTypes in
        throwError $ uncurry (TypeMismatch "Invalid argument types" pos) foo
    else
        ask
    where
        firstNotMatching (x:xs) (y:ys) = if x == y then firstNotMatching xs ys else (x, y)
        firstNotMatching _ _ = undefined

instance Checkable Expr where
    check (EApp pos ident exprs) = do
        env <- ask
        t <- getType pos ident
        case t of
            TFun pos2 retType argTypes -> do
                checkFunctionApplication pos retType argTypes exprs
            _ -> throwError $ NotAFunction pos
    -- check (EApp pos ident exprs) = do
    --     env <- ask
    --     t <- getType pos ident
    --     case t of
    --         TFun pos2 retType argTypes -> do
    --             Control.Monad.when (length exprs /= length argTypes) $ throwError $ WrongNumberOfArguments pos
    --             exprTypes <- mapM inspect exprs
    --             let argRawTypes = argTypes
    --             let exprLValue = map (\case { _ -> False }) exprs
    --             let argRef = map (\case { _ -> False }) argTypes
    --             if exprTypes /= argRawTypes then
    --                 let foo = firstNotMatching exprTypes argRawTypes in
    --                 throwError $ uncurry (TypeMismatch "Invalid argument types" pos) foo
    --             else if any (\(refNeeded, isLVal) -> refNeeded && not isLVal) $ zip argRef exprLValue then
    --                 throwError $ NotAnLValue pos
    --             else
    --                 ask
    --         _ -> throwError $ NotAFunction pos
    --     where
    --         firstNotMatching (x:xs) (y:ys) = if x == y then firstNotMatching xs ys else (x, y)
    --         firstNotMatching _ _ = undefined

    check (ELVal pos (LVar _ ident)) = do
        getType pos ident
        ask

    check (ELVal pos (LArrAcc pos2 expr_arr expr)) = do
        check expr_arr
        t <- inspect expr_arr
        check expr
        t' <- inspect expr
        case t' of
            TInt _ -> ask
            _ -> throwError $ TypeMismatch "Invalid index type" pos t' (TInt BNFC'NoPosition)

    check (ELVal pos (LAttrAcc pos2 expr ident)) = do
        check expr
        t <- inspect expr
        case t of
            TCls _ ident -> ask
            TArr _ _ -> if ident == Ident "length" then ask else throwError $ TypeMismatch "Arrays have no attributes" pos t (TCls BNFC'NoPosition ident)
            _ -> throwError $ TypeMismatch "Invalid attribute access" pos t (TCls BNFC'NoPosition ident)

    check (ERel pos expr1 op expr2) = do
        t1 <- inspect expr1
        t2 <- inspect expr2
        if t1 == t2 then
            case t1 of
                TVoid _ -> throwError $ TypeMismatch "Cannot compare void types!" pos t1 t2
                _ -> ask
        else throwError $ TypeMismatch "Incomparable types!" pos t1 t2

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

    check (ELitInt _ _) = ask
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
        check expr
        t' <- inspect expr
        case t' of
            TInt _ -> ask
            _ -> throwError $ TypeMismatch "Array size not an int!" pos t' (TInt BNFC'NoPosition)
    check (ENew pos ident) = do
        ask

    check (EMethodApply pos expr ident exprs) = do
        env <- ask
        t <- inspect expr
        case t of
            TCls _ clsname -> do
                let classes' = classes env
                case Map.lookup clsname classes' of
                    Just (base, classEnv) -> do
                        case Map.lookup ident classEnv of
                            Just (TFun pos2 retType argTypes) -> do
                                checkFunctionApplication pos retType argTypes exprs
                            Nothing -> throwError $ NoSuchAttribute pos ident
                    Nothing -> throwError $ UnknownIdentifier pos ident
            _ -> throwError $ TypeMismatch "Not a class!" pos t (TCls BNFC'NoPosition ident)

    check e = notImplemented e

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
    classes = Map.empty
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