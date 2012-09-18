{-# LANGUAGE FlexibleInstances #-}

{-
   This is an implementation of the Hindley Milner type inference
   algorithm from 
   'Generalizing Hindley Milner Type Inference Algorithms'.
-}

import Prelude hiding (foldl, map, filter, null)

import qualified Data.Map as Map
import Data.Set hiding (unions)
import Data.Maybe (fromMaybe)
import Control.Monad.State
import Data.Functor ((<$>))

type Id = String
type TVar = Int

data Expr = Abs Id Expr
          | Ap Expr Expr
          | Let Id Expr Expr
          | Var Id
          | ETrue | EFalse
          deriving (Eq, Ord)

data Type = Arrow Type Type
          | TVar TVar
          | TBool
          deriving (Eq, Ord)

data Scheme = Scheme TVars Type
            deriving (Show, Eq, Ord)

data Constraint = Equal Type Type
               | Implicit Type (Monos, Type)
               | Explicit Type Scheme
               deriving (Show, Eq, Ord)

type TVars = Set TVar
type Monos = TVars
type Assumptions = Map.Map Id TVars
type Constraints = Set Constraint
type Fresh = TVar
type TI = StateT Fresh (Either TCError)

data TCError = UnknownId Id
             | CantUnify Type Type
             | InfType TVar Type
             | CantSolve Constraints
             deriving (Show)

type Sub = Map.Map TVar Type


-- |The union of two sets
(∪) :: (Eq a, Ord a) => Set a -> Set a -> Set a
x ∪ y = x `union` y

-- |Intersection of two sets
(∩) :: (Eq a, Ord a) => Set a -> Set a -> Set a
x ∩ y = x `intersection` y

-- |Concat sets
unions :: (Eq a, Ord a) => Set (Set a) -> Set a
unions = foldl union empty

-- |Substitution constructor
subs :: TVar -> Type -> Sub
subs tv t = Map.singleton tv t

-- |Null substitution
nsub :: Sub
nsub = Map.empty

-- |The union of two assumption sets
aU :: Assumptions -> Assumptions -> Assumptions
aU = Map.unionWith (∪)

-- |Union of two Substitutions
-- s2 @@ s1  means perform s1, then s2
(@@) :: Sub -> Sub -> Sub
s2 @@ s1 = Map.map (sub s2) s1 `Map.union` s2

-- |Find a valid element and partition Set
findPart :: Ord a => (a -> Bool) -> Set a -> Maybe (a, Set a)
findPart cond cs = do
  (c, cs) <- minView cs
  if cond c
    then return (c, cs)
    else do
      (c', cs) <- findPart cond cs
      return (c', insert c cs)

class Subs a where
  ftv :: a -> TVars
  sub :: Sub -> a -> a

instance Subs TVars where
  ftv tvs = tvs
  sub s tvs = unions $ map (ftv . sub s . TVar) tvs

instance Subs Type where
  ftv t = case t of
    Arrow t1 t2 -> ftv t1 ∪ ftv t2
    TVar tv -> singleton tv
    t -> empty
  sub s t = case t of
    Arrow t1 t2 -> sub s t1 `Arrow` sub s t2
    TVar tv -> fromMaybe (TVar tv) (Map.lookup tv s)
    t -> t

instance Subs Scheme where
  ftv (Scheme m t) = ftv t \\ m
  sub s (Scheme m t) = Scheme m t'
    where t' = sub (foldl (flip Map.delete) s m) t

instance Subs Constraint where
  ftv _ = error "ftv <constraint>"
  sub s c = case c of
    Equal t1 t2 -> sub s t1 `Equal` sub s t2
    Implicit t1 (m, t2) -> sub s t1 `Implicit` (sub s m, sub s t2)
    Explicit t sc -> sub s t `Explicit` sub s sc

-- |Get the result of a computation in the TI Monad
runTI :: TI a -> Either TCError a
runTI x = fst <$> runStateT x 0

-- |Get a fresh type variable
fresh :: TI TVar
fresh = do
  fv <- get
  modify succ
  return fv

-- |Generate typing constraints from an Expression
bu :: Monos -> Expr -> TI (Assumptions, Constraints, Type)
bu ms e = case e of
  Ap e1 e2 -> do
    fv <- fresh
    (a1, c1, t1) <- bu ms e1
    (a2, c2, t2) <- bu ms e2
    let c3 = singleton (t1 `Equal` (t2 `Arrow` TVar fv))
    return (a1 `aU` a2, c1 ∪ c2 ∪ c3, TVar fv)
  Abs x e -> do
    fv <- fresh
    (a1, c1, t1) <- bu (fv `insert` ms) e
    let c2 = maybe empty (map (\t -> TVar t `Equal` TVar fv)) (Map.lookup x a1)
    return (Map.delete x a1, c1 ∪ c2, TVar fv `Arrow` t1)
  Let x e1 e2 -> do
    (a1, c1, t1) <- bu ms e1
    (a2, c2, t2) <- bu ms e2
    let c3 = maybe empty 
               (map (\t -> TVar t `Implicit` (ms, t1))) 
               (Map.lookup x a2)
    return (a1 `aU` Map.delete x a2, c1 ∪ c2 ∪ c3, t2)
  Var x -> do
    fv <- fresh
    return (Map.singleton x (singleton fv), empty, TVar fv)

  ETrue -> return (Map.empty, empty, TBool)
  EFalse -> return (Map.empty, empty, TBool)

-- |Find most general unifier
mgu :: Type -> Type -> Either TCError Sub
mgu t1 t2 = case (t1, t2) of
  (t1a `Arrow` t1r, t2a `Arrow` t2r) -> do
    s1 <- mgu t1a t2a
    s2 <- mgu (sub s1 t1r) (sub s1 t2r)
    return (s2 @@ s1)
  (TVar tv, t) -> checkInf tv t
  (t, TVar tv) -> checkInf tv t
  (t1, t2) | t1 == t2 -> return nsub
  _ -> Left $ CantUnify t1 t2
  where
    checkInf :: TVar -> Type -> Either TCError Sub
    checkInf tv t = case t of
      TVar tv2 | tv == tv2 -> return nsub
      t2 | tv `member` ftv t2 -> Left $ InfType tv t2
      t -> return (tv `subs` t)

-- |Active variables in a constraint
active :: Constraint -> TVars
active c = case c of
  Equal t1 t2 -> ftv t1 ∪ ftv t2
  Implicit t1 (m, t2) -> ftv t1 ∪ (m ∩ ftv t2)
  Explicit t sc -> ftv t ∪ ftv sc

-- |Generalize 
gen :: Monos -> Type -> Scheme
gen m t = Scheme (ftv t \\ m) t 

-- |Instantiate
inst :: Scheme -> TI Type
inst (Scheme m t) = do
  s <- foldl go (return Map.empty) m
  return (sub s t)
  where
    go :: TI Sub -> TVar -> TI Sub
    go s tv = do
      fv <- fresh
      Map.insert tv (TVar fv) <$> s

-- |Find the substitution that solves a set of constraints
solve :: Constraints -> TI Sub
solve cs | cs == empty = return nsub
         | Just (c, cs) <- findPart (valid cs) cs = solvec c cs
         | otherwise = lift $ Left $ CantSolve cs
  where
    solvec :: Constraint -> Constraints -> TI Sub
    solvec c cs = case c of
      Equal t1 t2 -> do
        s <- lift $ mgu t1 t2
        csc <- solve (map (sub s) cs)
        return (csc @@ s)
      Implicit t1 (m, t2) -> solve $ insert (Explicit t1 (gen m t2)) cs
      Explicit t1 sc -> do
        t2 <- inst sc
        solve $ insert (Equal t1 t2) cs

    valid cs c = case c of
      Implicit t1 (m, t2) -> null ((ftv t2 \\ m) ∩ activecs)
        where activecs = unions (map active (delete c cs))
      _ -> True


{-
 - QUICK AND DIRTY TESTS
-}

type_ :: Expr -> Either TCError Type
type_ e = runTI $ 
  do
    (as, cs, t) <- bu empty e
    s <- solve cs
    return $ sub s t

instance Show Type where
  show t = case t of
    Arrow t1 t2 -> unwords [braces t1, "->", show t2]
    TVar tv -> "t" ++ show tv
    TBool -> "Bool"
    where
      braces t = case t of
        Arrow t1 t2 -> concat ["(", show t, ")"]
        t -> show t

instance Show Expr where
  show t = case t of
    Abs x e -> concat ["\\", x, " -> ", show e]
    Ap e1 e2 -> unwords [braces e1, braces e2]
    Var x -> x
    Let x e1 e2 -> unwords ["let", x, "=", show e1, "in", show e2]
    ETrue -> "True"
    EFalse -> "False"
    where
      b e = concat ["(", show e, ")"]
      braces e = case e of
        Ap _ _ -> b e
        Abs _ _ -> b e
        Let _ _ _ -> b e
        _ -> show e

doTest e = do
  let t = case type_ e of
            Right t -> show t
            Left err -> "Error: " ++ show err
  putStrLn $ unwords [show e, "::", show t]
  
main = do

  doTest $ Let "x" (Abs "x" $ Var "x") (Ap (Var "x") (Ap (Var "x") (Var "x")))
  doTest $ Ap (Abs "x" $ Var "x") ETrue
  doTest $ Ap ETrue ETrue
