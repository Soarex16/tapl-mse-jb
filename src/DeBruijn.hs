module DeBruijn where

import qualified Data.Map as M
import Data.List

type Symb = String

infixl 4 :@:

infixl 4 :@

data Expr
  = Var Symb
  | Expr :@ Expr
  | Lam Symb Expr
  deriving (Eq, Read, Show)

data Term
  = Idx Int
  | Term :@: Term
  | Lmb Symb Term
  deriving (Read, Show)

instance Eq Term where
  Idx m == Idx n = m == n
  (t1 :@: s1) == (t2 :@: s2) = t1 == t2 && s1 == s2
  Lmb _ t1 == Lmb _ t2 = t1 == t2
  _ == _ = False

type Context = [Symb]

freeVars :: Expr -> M.Map Symb ()
freeVars (Var s) = M.singleton s ()
freeVars (m :@ n) = freeVars m `M.union` freeVars n
freeVars (Lam var body) = M.delete var (freeVars body)

extendwith :: Context -> Symb -> Context
extendwith ctx var
  | var `elem` ctx = extendwith ctx ('_' : var)
  | otherwise = var : ctx

t2e :: Context -> Term -> Expr
t2e ctx (Idx x) = Var (ctx !! x)
t2e ctx (m :@: n) = t2e ctx m :@ t2e ctx n
t2e ctx (Lmb var body) = let newCtx = ctx `extendwith` var in Lam (head newCtx) (t2e newCtx body)

e2t :: Expr -> (Context, Term)
e2t exp = (M.keys initialContext, go initialContext exp)
  where
    enumerate :: Ord a => M.Map a b -> M.Map a Int
    enumerate m = M.fromList $ zip (fst <$> M.toList m) [0..]
    initialContext = enumerate (freeVars exp)
    go :: M.Map Symb Int -> Expr -> Term
    go ctx (Var name) = maybe (Idx 0) Idx (name `M.lookup` ctx)
    go ctx (m :@ n) = go ctx m :@: go ctx n
    go ctx (Lam name body) = 
      let newCtx = M.insert name 0 (succ <$> ctx) 
      in Lmb name (go newCtx body)