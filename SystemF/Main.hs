{-
    This is a partial type inference algorithm for system F.
    It will try to infer the polymorphic argument type of a function when
    applying to it.
    It may be incomplete or flawed.
-}

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Data.Functor ((<$>))

type ID = String
type Error = String

data Type =
    TVar ID
  | Arrow Type Type
  | Forall ID Type
  | TUnit
  deriving (Show, Eq)

data Term =
    Var ID
  | Abs ID Type Term
  | Ap Term Term
  | TAbs ID Term
  | TAp Type Term
  | Unit
  deriving (Show, Eq)

-- (Type) variables -> Kind
type TCtx = Set.Set ID 

-- (Term) variables -> Type
type Ctx = Map.Map ID Type

type_ :: TCtx -> Ctx -> Term -> Either Error Type
type_ tctx ctx e = case e of
  Var x
    | (Just t) <- Map.lookup x ctx -> return t
    | otherwise -> Left $ x ++ ": unknown ident"
  Abs x t e -> do
    validType tctx t
    Arrow t <$> type_ tctx (Map.insert x t ctx) e 
  Ap e1 e2 -> do
    t1 <- type_ tctx ctx e1
    t2 <- type_ tctx ctx e2
    case t1 of
      Arrow ta tr
        | ta == t2  -> return tr
        | otherwise -> error "wrong arg applied"
--      Forall _ _ -> infer tctx t1 t2 >> error "ok"
      Forall _ _ -> infer tctx t1 t2
      otherwise -> error "ap to non func"
  TAbs x e -> Forall x <$> type_ (Set.insert x tctx) ctx e
  TAp t e -> do
    validType tctx t
    t2 <- type_ tctx ctx e
    case t2 of
      Forall x t2 -> return $ subs (Map.singleton x t) t2
      t2          -> error "Tap to non Forall"
  Unit -> return TUnit

validType :: TCtx -> Type -> Either Error ()
validType tctx t = case t of
  TVar x | Set.notMember x tctx -> Left $ x ++ ": type not in scope"
  Arrow t1 t2 -> validType tctx t1 >> validType tctx t2
  Forall x t -> validType (Set.insert x tctx) t
  t -> return ()

type Subs = Map.Map ID Type

subs :: Subs -> Type -> Type 
subs s t = case t of
  TVar x -> Map.findWithDefault (TVar x) x s
  Arrow t1 t2 -> Arrow (subs s t1) (subs s t2)
  Forall x t -> Forall x (subs (Map.delete x s) t)
  t -> t

-- The following code deals with type inference when applying to a generic
-- function.

infer :: TCtx -> Type -> Type -> Either Error Type
infer tctx t1 t2 = case t1 of
  Forall x t1 -> do
    let (x', t1') = renameIfNeeded x t1
    t <- infer (Set.insert x' tctx) t1' t2
    return $ if Set.member x' (free t) then Forall x' t else t
  Arrow ta tr -> do
    s <- unify ta t2
    return (subs s tr)
  where
    renameIfNeeded :: ID -> Type -> (ID, Type)
    renameIfNeeded x t1
      | Set.member x (free t2) = (fn, subs (Map.singleton x (TVar fn)) t1)
      | otherwise = (x, t1)
        where fn = freshName (Set.insert x tctx) x

    freshName :: Set.Set ID -> ID -> ID
    freshName xs x
      | Set.member x xs = freshName xs (x ++ "'")
      | otherwise       = x

free :: Type -> Set.Set ID
free t = case t of
  TVar x -> Set.singleton x
  Arrow t1 t2 -> Set.union (free t1) (free t2)
  Forall x t -> Set.delete x (free t)
  t -> Set.empty

-- |Union of two Substitutions
-- s2 @@ s1 means perform s1, then s2
(@@) :: Subs -> Subs -> Subs
s2 @@ s1 = Map.union (Map.map (subs s2) s1) s2

unify :: Type -> Type -> Either Error Subs
unify t1 t2 = case (t1, t2) of
  (Arrow t1a t1r, Arrow t2a t2r) -> do
    s1 <- unify t1a t2a
    s2 <- unify t1r t2r
    return (s2 @@ s1)
  (TVar x, t) -> checkInf x t
  (t, TVar x) -> checkInf x t
  (Forall x t1, Forall y t2) -> error "not yet"    
  (t1, t2) | t1 == t2 -> return Map.empty
  _ -> Left $ "cant unify " ++ show t1 ++ " and " ++ show t2
  where
    checkInf x t = case t of
      TVar y | x == y -> return Map.empty
      t | Set.member x (free t) -> error "inf type"
      t -> return (Map.singleton x t)



-- test stuff below

ide = TAbs "X" $ Abs "x" (TVar "X") $ Var "x"
conste = TAbs "X" $ TAbs "Y" $ 
  Abs "x" (TVar "X") $ Abs "y" (TVar "Y") $ Var "x"
conste2 = TAbs "X" $ Abs "x" (TVar "X") $ 
  TAbs "Y" $ Abs "y" (TVar "Y") $ Var "x"

(Right constet) = test conste
(Right idet) = test ide

test = type_ Set.empty Map.empty
 
