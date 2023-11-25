{-# LANGUAGE FlexibleInstances, LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}

module TypeChecker (typeCheck) where

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
import Control.Exception (throw)
import Data.Data (Typeable)
import Control.Exception.Base (Exception)
import GHC.Stack (HasCallStack)
import Control.Monad (foldM)
import qualified Data.Set as Data

type TypeEnv = Map Ident Type

data CheckEnv = CheckEnv {
    typeEnv :: !TypeEnv,
    retType :: !(Maybe Type),
    inLoop :: !Bool
}

modifyEnv :: (TypeEnv -> TypeEnv) -> CheckEnv -> CheckEnv
modifyEnv f env = env { typeEnv = f (typeEnv env) }

assignType :: Ident -> Type -> CheckEnv -> CheckEnv
assignType ident t = modifyEnv (Map.insert ident t)

assignTypes :: [(Ident, Type)] -> CheckEnv -> CheckEnv
assignTypes = flip $ foldr (uncurry assignType)

getArgType :: ArgC -> Type
getArgType (Arg _ t _) = t
-- getArgType (ArgRef _ t _) = t

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
    | RepeatedDeclaration !a
    deriving (Typeable)

instance {-# OVERLAPPING #-} Show BNFC'Position where
    show BNFC'NoPosition = ""
    show (BNFC'Position l c) = "(Line " ++ show l ++ ", column " ++ show c ++ ")"
    show _ = ""

instance {-# OVERLAPPING #-} Show Type where
    show (Int _) = "int"
    show (Str _) = "string"
    show (Bool _) = "bool"
    show (Void _) = "void"
    show (Fun _ retType argTypes) = show retType ++ "(" ++ show argTypes ++ ")"

instance Show Exc where
    show (UnknownIdentifier pos ident) = "Unknown identifier " ++ show ident ++ " at " ++ show pos
    show (InvalidReturn pos) = "Invalid return at " ++ show pos
    show (InvalidBreak pos) = "Invalid break at " ++ show pos
    show (InvalidContinue pos) = "Invalid continue at " ++ show pos
    show (NotAFunction pos) = "Not a function at " ++ show pos
    show (TypeMismatch msg pos actual expected) = show msg ++ "Type mismatch at " ++ show pos ++ ": " ++ "expected " ++ show expected ++ ", got " ++ show actual
    show (WrongNumberOfArguments pos) = "Wrong number of arguments at " ++ show pos
    show (TCNotImplemented pos msg) = "Not implemented at " ++ show pos ++ ": " ++ msg
    show (NotAnLValue pos) = "Not an lvalue at " ++ show pos
instance Exception Exc

type IM = ReaderT CheckEnv (ExceptT Exc Identity)

evalMaybe :: Exc -> Maybe a -> IM a
evalMaybe e Nothing = throwError e
evalMaybe _ (Just a) = pure a

getType :: BNFC'Position -> Ident -> IM Type
getType pos ident = do
    env <- ask
    evalMaybe (UnknownIdentifier pos ident) (Map.lookup ident (typeEnv env))

inspect :: Expr -> IM Type
inspect (ELitInt pos _) = return $ Int pos
inspect (EString pos _) = return $ Str pos
inspect (ELitTrue pos) = return $ Bool pos
inspect (ELitFalse pos) = return $ Bool pos
inspect (ERel pos lhs _ rhs) = return $ Bool pos
-- inspect (ELVal pos (LIdent _ ident)) = getType pos ident
inspect (EVar pos ident) = getType pos ident
inspect (EAdd pos lhs _ rhs) = inspect lhs
inspect (EMul pos lhs _ rhs) = return $ Int pos
inspect (ENeg pos expr) = return $ Int pos
inspect (EApp pos ident args) = do
    t <- getType pos ident
    case t of
        Fun _ retType argTypes -> return retType
        _ -> throwError $ NotAFunction pos
inspect (EAnd pos lhs rhs) = return $ Bool pos
inspect (EOr pos lhs rhs) = return $ Bool pos
inspect (ENot pos expr) = return $ Bool pos
inspect (ENewArr pos t expr) = return $ Arr pos t
inspect (ENew pos ident) = getType pos ident
-- inspect (EAt pos expr1 expr2) = do
--     t1 <- inspect expr1
--     t2 <- inspect expr2
--     case t1 of
--         Str _ -> case t2 of
--             Int _ -> return $ Str pos
--             _ -> throwError $ TypeMismatch "eat" pos t1 t2
--         _ -> throwError $ TypeMismatch "eat" pos t1 t2
inspect e = notImplemented e

notImplemented :: (Show a) => a -> IM b
notImplemented x = throwError $ TCNotImplemented BNFC'NoPosition $ show x

instance {-# OVERLAPPING #-} Eq Type where
    Int _ == Int _ = True
    Str _ == Str _ = True
    Bool _ == Bool _ = True
    Void _ == Void _ = True
    Fun _ retType1 argTypes1 == Fun _ retType2 argTypes2 = retType1 == retType2 && argTypes1 == argTypes2
    _ == _ = False

instance {-# OVERLAPPING #-} Eq ArgC where
    (==) :: ArgC -> ArgC -> Bool
    Arg _ t1 _ == Arg _ t2 _ = t1 == t2

class Checkable a where
    check :: a -> IM CheckEnv

instance Checkable ProgramC where
    -- take into account that function can be defined after it is used
    check (Program _ topDefs) = do
        env <- ask
        let env' = assignTypes (map (\(FunDecl _ (FunDef _ retType ident args _)) -> (ident, Fun BNFC'NoPosition retType args)) topDefs) env
        foldM (\env' topDef -> local (const env') (check topDef)) env' topDefs


instance Checkable BlockC where
    check (Block _ stmts) = do
        -- check if names in declarations are unique
        -- if any is not unique, print its position
        let decls = filter (\case { Decl {} -> True ; _ -> False }) stmts
        let declNamesPositions = concatMap (\(Decl _ _ items) -> map (\case { NoInit pos ident -> (ident, pos) ; Init pos ident _ -> (ident, pos) }) items) decls
    
        foldM_ (\localNames namePosition -> do
            let (name, pos) = namePosition
            if Data.member name localNames then
                throwError $ RepeatedDeclaration pos
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
        isReturn (VRet _) = True
        isReturn (Ret _ _) = True
        isReturn (CondElse _ (ELitTrue _) stmt _) = isReturn stmt
        isReturn (CondElse _ (ELitFalse _) _ stmt) = isReturn stmt
        isReturn (CondElse _ _ stmt1 stmt2) = isReturn stmt1 && isReturn stmt2
        isReturn (Cond _ (ELitTrue _) stmt) = isReturn stmt
        isReturn (Cond _ _ stmt) = False
        isReturn (BStmt _ block) = hasReturn block
        isReturn (While _ (ELitTrue _) stmt) = isReturn stmt
        isReturn _ = False


instance Checkable TopDef where
    check (FunDecl _ (FunDef pos retType ident args block)) = do
        env <- ask
        argNames <- mapM (\(Arg _ _ ident) -> return ident) args
        Control.Monad.when (nub argNames /= argNames) $ throwError $ InvalidReturn pos
        let funType = Fun pos retType args
        let env' = assignType ident funType env        
        local (const $ bindArgs args $ env' {retType = Just retType}) (check block)

        case retType of
            Void _ -> return env'
            _ -> if hasReturn block then return env' else throwError $ InvalidReturn pos
        
        where
            bindArgs :: [ArgC] -> CheckEnv -> CheckEnv
            bindArgs args = assignTypes $ map (\arg -> (getIdent arg, getArgType arg)) args
            getIdent :: ArgC -> Ident
            getIdent (Arg _ _ ident) = ident
    
    check t = notImplemented t

    -- check (ClassDecl pos ident classItems) = do
    --     env <- ask
    --     let env' = assignType ident (Cls pos ident) env
    --     foldM (\env' classItem -> local (const env') (check classItem)) env' classItems


instance Checkable Stmt where
    check (Empty _) = ask
    check (BStmt _ block) = do
        env <- ask
        local (const env {inLoop = False}) (check block)
    check (SExp _ expr) = do
        check expr
        ask
    check (Incr pos expr) = do
        check expr
        t <- inspect expr
        case t of
            Int _ -> ask
            _ -> throwError $ TypeMismatch "incr" pos t (Int BNFC'NoPosition)
    check (Decr pos expr) = do
        check expr
        t <- inspect expr
        case t of
            Int _ -> ask
            _ -> throwError $ TypeMismatch "decr" pos t (Int BNFC'NoPosition)
    check (VRet pos) = do
        env <- ask
        case retType env of
            Nothing -> throwError $ InvalidReturn pos
            Just (Void _) -> ask
            Just t -> throwError $ TypeMismatch "vret" pos t (Void BNFC'NoPosition)
    check (Ret pos expr) = do
        env <- ask
        case retType env of
            Nothing -> throwError $ InvalidReturn pos
            Just t -> do
                check expr
                t' <- inspect expr
                if t == t' then return env else throwError $ TypeMismatch "ret" pos t t'
    
    check (Decl pos t items) = do
        env <- ask
        foldM (\env' item -> local (const env') (check_item item)) env items

        where
        check_item (Init pos ident expr) = do
            env <- ask
            check expr
            t' <- inspect expr
            if t == t' then return $ assignType ident t env else throwError $ TypeMismatch "decl" pos t t'
        
        check_item (NoInit _ ident) = asks $ assignType ident t

    check (CondElse pos expr stmt1 stmt2) = do
        check expr
        t <- inspect expr
        case t of
            Bool _ -> do
                check stmt1
                check stmt2
            _ -> throwError $ TypeMismatch "condelse" pos t (Bool BNFC'NoPosition)
    check (Cond pos expr stmt) = do
                check expr
                t <- inspect expr
                case t of
                    Bool _ -> check stmt
                    _ -> throwError $ TypeMismatch "cond" pos t (Bool BNFC'NoPosition)
    -- check (Ass pos (LIdent pos2 ident) expr) = do
    check (Ass pos (EVar pos2 ident) expr) = do
        t1 <- getType pos2 ident
        check expr
        t2 <- inspect expr
        if t1 == t2 then ask else throwError $ TypeMismatch "ass" pos t1 t2
    check (While pos expr block) = do
        check expr
        t <- inspect expr
        case t of
            Bool _ -> check block
            _ -> throwError $ TypeMismatch "while" pos t (Bool BNFC'NoPosition)
    check e = notImplemented e

instance Checkable Expr where
    check (EApp pos ident exprs) = do
        env <- ask
        t <- getType pos ident
        case t of
            Fun pos2 retType argTypes -> do
                Control.Monad.when (length exprs /= length argTypes) $ throwError $ WrongNumberOfArguments pos
                exprTypes <- mapM inspect exprs
                let argRawTypes = map getArgType argTypes
                -- let exprLValue = map (\case { ELVal _ _ -> True ; _ -> False }) exprs
                let exprLValue = map (\case { _ -> False }) exprs
                -- let argRef = map (\case { ArgRef {} -> True ; _ -> False }) argTypes
                let argRef = map (\case { _ -> False }) argTypes
                if exprTypes /= argRawTypes then
                    let foo = firstNotMatching exprTypes argRawTypes in
                    throwError $ uncurry (TypeMismatch "eapp" pos) foo
                else if any (\(refNeeded, isLVal) -> refNeeded && not isLVal) $ zip argRef exprLValue then
                    throwError $ NotAnLValue pos
                else
                    ask
            _ -> throwError $ NotAFunction pos
        where
            firstNotMatching (x:xs) (y:ys) = if x == y then firstNotMatching xs ys else (x, y)
            firstNotMatching _ _ = undefined
    check (EVar pos ident) = do
        getType pos ident
        ask
    check (ERel pos expr1 op expr2) = do
        t1 <- inspect expr1
        t2 <- inspect expr2
        if t1 == t2 then ask else throwError $ TypeMismatch "erel" pos t1 t2
    check (ENeg pos expr) = do
        check expr
        t <- inspect expr
        case t of
            Int _ -> ask
            _ -> throwError $ TypeMismatch "eneg" pos t (Int BNFC'NoPosition)
    
    check (EAdd pos expr1 op expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            Int _ -> case t2 of
                Int _ -> ask
                _ -> throwError $ TypeMismatch "eadd" pos t1 t2
            Str _ -> case t2 of
                Str _ -> ask
                _ -> throwError $ TypeMismatch "eadd" pos t1 t2
            _ -> throwError $ TypeMismatch "eadd" pos t1 t2
    check (EMul pos expr1 op expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            Int _ -> case t2 of
                Int _ -> ask
                _ -> throwError $ TypeMismatch "emul" pos t1 t2
            _ -> throwError $ TypeMismatch "emul" pos t1 t2
    -- check (ELVal _ _ ) = ask
    check (ELitInt _ _) = ask
    check (EString _ _) = ask
    check (ELitTrue _) = ask
    check (ELitFalse _) = ask
    check (ENot pos expr) = do
        check expr
        t <- inspect expr
        case t of
            Bool _ -> ask
            _ -> throwError $ TypeMismatch "enot" pos t (Bool BNFC'NoPosition)
    check (EOr pos expr1 expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            Bool _ -> case t2 of
                Bool _ -> ask
                _ -> throwError $ TypeMismatch "eor" pos t1 t2
            _ -> throwError $ TypeMismatch "eor" pos t1 t2
    check (EAnd pos expr1 expr2) = do
        check expr1
        t1 <- inspect expr1
        check expr2
        t2 <- inspect expr2
        case t1 of
            Bool _ -> case t2 of
                Bool _ -> ask
                _ -> throwError $ TypeMismatch "eand" pos t1 t2
            _ -> throwError $ TypeMismatch "eand" pos t1 t2
    
    check (ENewArr pos t expr) = do
        check expr
        t' <- inspect expr
        case t' of
            Int _ -> ask
            _ -> throwError $ TypeMismatch "enewarr" pos t' (Int BNFC'NoPosition)
    check (ENew pos ident) = do
        getType pos ident
        ask
    check e = notImplemented e

typeCheck :: ProgramC -> IO ()
typeCheck p = do
    case runIdentity $ runExceptT $ runReaderT (check p) initEnv of
        Left err -> throw err
        Right env -> return ()
    where
        initEnv = CheckEnv {
            typeEnv = Map.fromList [
                (Ident "print", Fun BNFC'NoPosition (Void BNFC'NoPosition) [Arg BNFC'NoPosition (Str BNFC'NoPosition) (Ident "_")]),
                (Ident "printString", Fun BNFC'NoPosition (Void BNFC'NoPosition) [Arg BNFC'NoPosition (Str BNFC'NoPosition) (Ident "_")]),
                (Ident "printInt", Fun BNFC'NoPosition (Void BNFC'NoPosition) [Arg BNFC'NoPosition (Int BNFC'NoPosition) (Ident "_")]),
                (Ident "atoi", Fun BNFC'NoPosition (Int BNFC'NoPosition) [Arg BNFC'NoPosition (Str BNFC'NoPosition) (Ident "_")]),
                (Ident "readInt", Fun BNFC'NoPosition (Int BNFC'NoPosition) []),
                (Ident "readString", Fun BNFC'NoPosition (Str BNFC'NoPosition) [])
                -- (Ident "error", Fun BNFC'NoPosition (Int BNFC'NoPosition) []),
                -- (Ident "readInt", Fun BNFC'NoPosition (Int BNFC'NoPosition) []),
                -- (Ident "readString", Fun BNFC'NoPosition (Str BNFC'NoPosition) [])
            ],
            retType = Nothing,
            inLoop = False
        }