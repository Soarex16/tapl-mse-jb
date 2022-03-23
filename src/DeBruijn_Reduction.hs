module DeBruijn_Reduction where
import Control.Applicative

infixl 4 :@:

data Term = Idx Int
          | Term :@: Term
          | Lmb Term
          deriving (Eq, Read, Show)

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