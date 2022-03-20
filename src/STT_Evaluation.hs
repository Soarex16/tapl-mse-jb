module STT_Evaluation where

import Data.Foldable
import Debug.Trace

type Symb = String
infixl 4 :@:
infixr 3 :->
infixl 5 :*
infixl 4 :+

data Type = Boo
          | Nat
          | Type :-> Type
          | Type :* Type
          | Type :+ Type  -- !!
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Fix Term
          | Inl Term Type              -- !!
          | Inr Type Term              -- !!
          | Case Term Symb Term Term   -- !!
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls                 =  True
  Tru       == Tru                 =  True
  If b u w  == If b1 u1 w1         =  b == b1 && u == u1 && w == w1
  Zero      == Zero                =  True
  Succ u    == Succ u1             =  u == u1
  Pred u    == Pred u1             =  u == u1
  IsZero u  == IsZero u1           =  u == u1
  Idx m     == Idx m1              =  m == m1
  (u:@:w)   == (u1:@:w1)           =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1         =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1        =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1          =  u == u1 && w == w1
  Fst z     == Fst z1              =  z == z1
  Snd z     == Snd z1              =  z == z1
  Fix u     == Fix u1              =  u == u1
  Inl u t   == Inl u1 t1           =  u == u1 &&  t == t1           -- !
  Inr t u   == Inr t1 u1           =  t == t1 && u == u1            -- !
  Case u _ t s == Case u1 _ t1 s1  =  u == u1 && t == t1 && s == s1 -- !
  _         == _                   =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

isNV :: Term -> Bool
isNV Zero = True
isNV (Succ x) = isNV x
isNV _ = False

shift :: Int -> Term -> Term
shift val = go val 0
    where
        go :: Int -> Int -> Term -> Term
        go off th (If b t e) = let f = go off th in If (f b) (f t) (f e)
        go off th (Idx n) = Idx $ if n < th then n else n + off
        go off th (p :@: q) = go off th p :@: go off th q
        go off th (Lmb s t p) = Lmb s t $ go off (th + 1) p
        go off th (Let p u w) = Let p (go off th u) (go off (th + patternSize p) w)
        go off th (Pair p q) = Pair (go off th p) (go off th q)
        go off th (Fst t) = Fst (go off th t)
        go off th (Snd t) = Snd (go off th t)
        go off th (Succ t) = Succ (go off th t)
        go off th (Pred t) = Pred (go off th t)
        go off th (IsZero t) = IsZero (go off th t)
        go off th (Fix t) = Fix (go off th t)
        go off th (Inl u tR) = Inl (go off th u) tR
        go off th (Inr tL u) = Inr tL (go off th u)
        go off th (Case v x l r) = Case v x (go off (th + 1) l) (go off (th + 1) r)
        go off th t = t

substDB :: Int -> Term -> Term -> Term
substDB j s (If b t e) = let f = substDB j s in If (f b) (f t) (f e)
substDB j s (Idx n) = if j == n then s else Idx n
substDB j s (p :@: q) = substDB j s p :@: substDB j s q
substDB j s (Lmb v t p) = Lmb v t $ substDB (j + 1) (shift 1 s) p
substDB j s (Pair p q) = Pair (substDB j s p) (substDB j s q)
substDB j s (Fst t) = Fst (substDB j s t)
substDB j s (Snd t) = Snd (substDB j s t)
substDB j s (Fix t) = Fix (substDB j s t)
substDB j s (Succ t) = Succ (substDB j s t)
substDB j s (Pred t) = Pred (substDB j s t)
substDB j s (IsZero t) = IsZero (substDB j s t)
substDB j s (Let p u w) = let
  offset = patternSize p
  in Let p (substDB j s u) (substDB (j + offset) (shift offset s) w)
substDB j s (Inl u tR) = Inl (substDB j s u) tR
substDB j s (Inr tL u) = Inr tL (substDB j s u)
substDB j s (Case v x l r) = let s' = shift 1 s; go = substDB (j + 1) s' in Case (substDB j s v) x (go l) (go r)
substDB j s t = t

patternSize :: Pat -> Int
patternSize (PVar _) = 1
patternSize (PPair f s) = patternSize f + patternSize s

isValue :: Term -> Bool
isValue Fls = True
isValue Tru = True
isValue Lmb {} = True
isValue (Pair x y) = isValue x && isValue y
isValue n | isNV n = True
isValue (Inl u _) = isValue u
isValue (Inr _ u) = isValue u
isValue _ = False

match :: Pat -> Term -> Maybe [(Symb,Term)]
match (PVar x) u | isValue u = Just [(x, u)]
match (PPair fst snd) (Pair x y) = do
  fstMatch <- match fst x
  sndMatch <- match snd y
  pure (fstMatch ++ sndMatch) -- name collision?
match _ _ = Nothing

betaRuleDB :: Term -> Term
betaRuleDB (Lmb v t b :@: s) = substituteOnce b s
betaRuleDB x = x

substituteOnce t s = let
  s' = shift 1 s
  t' = substDB 0 s' t
  in shift (-1) t'

substituteAll :: Term -> [Term] -> Term
substituteAll = foldl' substituteOnce

oneStep :: Term -> Maybe Term
oneStep (If cond t e) = case cond of
  Tru -> {- trace "E-IfTrue" -} Just t
  Fls -> {- trace "E-IfFalse" -} Just e
  c -> {- trace "E-If" -} (\b' -> If b' t e) <$> oneStep cond
oneStep r@((Lmb v t m) :@: n)
  | isValue n = {- trace "E-AppAbs" -} Just (betaRuleDB r)
  | otherwise = {- trace "E-App2" -} ((Lmb v t m :@:) <$> oneStep n)
oneStep (m :@: n) = {- trace "E-App1" -} ((:@: n) <$> oneStep m)
oneStep (Fst p@(Pair x y))
  | isValue x && isValue y = {- trace "E-PairBeta1" -} Just x
  | otherwise = {- trace "E-Proj1" -} Fst <$> oneStep p
oneStep (Snd p@(Pair x y))
  | isValue x && isValue y = {- trace "E-PairBeta1" -} Just y
  | otherwise = {- trace "E-Proj1" -} Snd <$> oneStep p
oneStep (Pair x y)
  | isValue x = {- trace "E-Pair2" -} Pair x <$> oneStep y
  | otherwise = {- trace "E-Pair1" -} (`Pair` y) <$> oneStep x
oneStep (Let p v t)
  | isValue v = {- trace "E-LetV" -} substituteAll t . reverse <$> (fmap . fmap) snd (match p v)
  | otherwise = {- trace "E-Let" -} (\v' -> Let p v' t) <$> oneStep v
oneStep (Succ t) = {- trace "E-Succ" -} Succ <$> oneStep t
oneStep (Pred n) = case n of
  Zero -> {- trace "E-PredZero" -} Just Zero
  Succ t | isNV t -> {- trace "E-PredSucc" -} Just t
  t -> {- trace "E-Pred" -} Pred <$> oneStep t
oneStep (IsZero t) = case t of
  Zero -> {- trace "E-IsZeroZero" -} Just Tru
  Succ n | isNV n -> {- trace "E-IsZeroSucc" -} Just Fls
  _ -> {- trace "E-IsZero" -} IsZero <$> oneStep t
oneStep f@(Fix t) = case t of
  Lmb _ _ b -> {- trace "E-FixBeta" -} Just $ substituteOnce b f
  t -> {- trace "E-Fix" -} Fix <$> oneStep t
oneStep (Case t x l r) = case t of
  Inl v _ | isValue v -> {- trace "E-CaseInl" -} Just $ substituteOnce l v
  Inr _ v | isValue v -> {- trace "E-CaseInr" -} Just $ substituteOnce r v
  t -> {- trace "E-Case" -} (\t' -> Case t' x l r) <$> oneStep t
oneStep (Inl t tR) = {- trace "E-Inl" -} (`Inl` tR) <$> oneStep t
oneStep (Inr tL t) = {- trace "E-Inr" -} (Inr tL) <$> oneStep t
oneStep t = trace ("E-Otherwise {{" ++ show t ++ "}}") Nothing

whnf :: Term -> Term
whnf u = trace ("term: " ++ show u) maybe u whnf (oneStep u)