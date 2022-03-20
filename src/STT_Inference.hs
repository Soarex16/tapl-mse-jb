module STT_Inference where

import Control.Monad (guard)

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

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar x) t = Just $ Env [(x, t)]
checkPat (PPair f s) (x :* y) = do
  Env fstEnv <- checkPat f x
  Env sndEnv <- checkPat s y
  pure $ Env $ sndEnv ++ fstEnv
checkPat _ _ = Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

infer :: Env -> Term -> Maybe Type
infer env Fls = Just Boo
infer env Tru = Just Boo
infer env (If b t e) = do
    Boo <- infer env b
    tType <- infer env t
    eType <- infer env e
    guard (tType == eType)
    pure eType
infer (Env env) (Idx v) = Just (snd (env !! v))
infer (Env env) (Lmb v t b) = do
    let env' = Env $ (v, t):env
    bodyType <- infer env' b
    pure (t :-> bodyType)
infer env (m :@: n) = do
    t :-> s <- infer env m
    argType <- infer env n
    guard (t == argType)
    pure s
infer (Env env) (Let pat letExpr w) = do
    letExpressionType <- infer (Env env) letExpr
    Env patternEnv <- checkPat pat letExpressionType
    let newEnv = Env $ patternEnv ++ env
    infer newEnv w
infer env (Pair f s) = do
    fstType <- infer env f
    sndType <- infer env s
    pure (fstType :* sndType)
infer env (Fst t) = do
    fstType :* sndType <- infer env t
    pure fstType
infer env (Snd t) = do
    fstType :* sndType <- infer env t
    pure sndType
infer env Zero = Just Nat
infer env (Succ t) = do
    Nat <- infer env t
    pure Nat
infer env (Pred t) = do
    Nat <- infer env t
    pure Nat
infer env (IsZero t) = do
    Nat <- infer env t
    pure Boo
infer env (Fix t) = do
    argType :-> retType <- infer env t
    guard (argType == retType)
    pure retType
infer env (Inl t tR) = do
    leftType <- infer env t
    pure (leftType :+ tR)
infer env (Inr tL t) = do
    rightType <- infer env t
    pure (tL :+ rightType)
infer env@(Env e) (Case t s l r) = do
    caseLType :+ caseRType <- infer env t
    leftType <- infer (Env $ (s, caseLType):e) l
    rightType <- infer (Env $ (s, caseRType):e) r
    guard (leftType == rightType)
    pure leftType