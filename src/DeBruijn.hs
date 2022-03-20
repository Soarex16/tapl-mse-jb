module DeBruijn where

import Control.Applicative
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

shift :: Int -> Term -> Term
shift val = go val 0
    where
        go :: Int -> Int -> Term -> Term
        go k m (Idx n) = Idx $ if n < m then n else n + k
        go k m (p :@: q) = go k m p :@: go k m q
        go k m (Lmb p) = Lmb $ go k (m + 1) p

substDB :: Int -> Term -> Term -> Term
substDB j s (Idx n) = if j == n then s else Idx n
substDB j s (p :@: q) = substDB j s p :@: substDB j s q
substDB j s (Lmb p) = Lmb $ substDB (j + 1) (shift 1 s) p

betaRuleDB :: Term -> Term
betaRuleDB (Lmb t :@: s) =
    let
        s' = shift 1 s
        t' = substDB 0 s' t
        in shift (-1) t'
betaRuleDB x = x

oneStepDBN :: Term -> Maybe Term
oneStepDBN (Idx n) = Nothing -- app1
oneStepDBN (Lmb n) = Lmb <$> oneStepDBN n -- abs
oneStepDBN t@(Lmb m :@: n) = Just $ betaRuleDB t -- app abs
oneStepDBN (m :@: n) = ((:@: n) <$> oneStepDBN m) <|> ((m :@:) <$> oneStepDBN n)  -- app1

oneStepDBA :: Term -> Maybe Term
oneStepDBA (Idx n) = Nothing
oneStepDBA (Lmb n) = Lmb <$> oneStepDBA n
oneStepDBA t@(Lmb m :@: n) = ((Lmb m :@:) <$> oneStepDBA n) <|> Just (betaRuleDB t)
oneStepDBA (m :@: n) = ((:@: n) <$> oneStepDBA m) <|> ((m :@:) <$> oneStepDBA n)

nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = maybe t (nfDB f) $ f t

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
t2e ctx (Lmb var body) = let newCtx = ctx `extendwith` var in Lam var (t2e newCtx body)

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