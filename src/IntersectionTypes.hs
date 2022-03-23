module IntersectionTypes where

import qualified Data.Set as S
import Data.Function
import Data.List
import Data.Foldable
import Control.Monad (guard)
import Data.Maybe
import Control.Monad.State
import Control.Monad.Identity (Identity)

type Symb = String
-- Типы-пересечения (1 способ)
infixr 4 :->
infixr 5 :/\
data Type = TVar Symb         -- типовой атом 
          | Type :-> Type     -- стрелочный тип
          | Type :/\ Type     -- тип пересечение
          | Univ              -- универсальный тип
    deriving (Read,Show)
-- Типы-пересечения (2 способ)
newtype IType = I [SType]      -- тип-пересечение 
    deriving (Read,Show,Ord)
-- Простые типы
infixr 4 :-->
data SType = STVar Symb        -- типовой атом 
           | IType :--> IType  -- стрелочный тип
    deriving (Read,Show,Eq,Ord)

instance Eq Type where
  (==) = (==) `on` toI

instance Eq IType where
  I x == I y = f x == f y
    where f = nub . sort

toI :: Type -> IType
toI (TVar x) = I [STVar x]
toI (u :-> v) = I [toI u :--> toI v]
toI (u :/\ v) =
    let (I uT) = toI u
        (I vT) = toI v
        in I (uT ++ vT)
toI Univ = I []

fromI :: IType -> Type
fromI (I []) = Univ
fromI (I ts) = foldr1 (:/\) (sToI <$> ts)
    where
        sToI :: SType -> Type
        sToI (STVar x) = TVar x
        sToI (u :--> v) = fromI u :-> fromI v

collectTVars :: IType -> S.Set Symb
collectTVars (I []) = S.empty
collectTVars (I xs) = foldr1 S.union (collectSTVars <$> xs)

collectSTVars :: SType -> S.Set Symb
collectSTVars (STVar v) = S.singleton v
collectSTVars (u :--> v) = collectTVars u `S.union` collectTVars v

subsAllI ns ms (I xs) = I (subsAllS ns ms <$> xs)

subsAllS fs ts (STVar v) = STVar (ts !! fromJust (elemIndex v fs))
subsAllS fs ts (x :--> y) = subsAllI fs ts x :--> subsAllI fs ts y

alphaEqTy :: Type -> Type -> Bool
alphaEqTy = alphaEqITy `on` toI

alphaEqITy :: IType -> IType -> Bool
alphaEqITy x y = length xVars == length yVars && elem y ((\p -> subsAllI xVars p x) <$> permutations yVars)
  where
    getVars = S.toList . collectTVars
    xVars = getVars x
    yVars = getVars y

alphaEqSTy :: SType -> SType -> Bool
alphaEqSTy x y = length xVars == length yVars &&  elem y ((\p -> subsAllS xVars p x) <$> permutations yVars)
  where
    getVars = S.toList . collectSTVars
    xVars = getVars x
    yVars = getVars y

type Ctx = [[Type]]    -- контекст

data TermNF = Trm
              Int      -- абстрактор (число биндеров)
              Int      -- головная переменная (индекс де Брауна)
              [TermNF] -- аргументы (Бёмовы хвостики)
    deriving (Read,Show,Eq,Ord)

-------------------------------------
infer :: TermNF -> (Ctx, Type)
infer tnf = evalState (inferType initialCtx tnf) 0
  where 
    initialCtx = replicate (countFreeVars tnf) []

inferType :: Monad m => Ctx -> TermNF -> StateT Int m (Ctx, Type)
inferType env t@(Trm absCnt absId tails) = do
  let envWithAbsVars = replicate absCnt [] ++ env
  let f (r, e) t = do { (e', t) <- inferType e t; pure (t:r, e') }
  (tailTypes, extendedEnv) <- foldlM f ([], envWithAbsVars) tails
  xRetType <- makeNewSymbol -- Выбираем свежее имя переменной для типа тела нашего терма
  let xType = makeArrowType tailTypes xRetType -- Приписываем головной переменной согласованный с аппликативной структурой тела стрелочный тип
  let resultCtx = modifyNth absId (xType:) extendedEnv -- Находим переменную в контексте и добавляем новый тип, как элемент пересечения
  let xAppType = curryFrom (take absCnt resultCtx) xRetType
  pure (drop absCnt resultCtx, xAppType)

countFreeVars :: TermNF -> Int
countFreeVars t = S.size (go 0 S.empty t)
  where
    go d refs (Trm absCnt absId tails) = let
      newRefs = S.map (+absCnt) refs
      newRefs' = if absId >= newDepth then S.insert absId newRefs else newRefs
      newDepth = d + absCnt
      in foldr (flip (go newDepth)) newRefs' tails

modifyNth :: Int -> (a -> a) -> [a] -> [a]
modifyNth n f l = (\(el, idx) -> if idx == n then f el else el) <$> zip l [0..]

makeArrowType xs t = foldl (flip (:->)) t xs

makeIntersectionType [] = Univ
makeIntersectionType ts = foldr1 (:/\) ts

makeNewSymbol :: Monad m => StateT Int m Type
makeNewSymbol = do
    a <- get
    modify succ
    return $ TVar (show a)

-- для комбинаторов достаточно
infer0 :: TermNF -> Type
infer0 = snd . infer

curryFrom :: Ctx -> Type -> Type
curryFrom ctx = makeArrowType (makeIntersectionType <$> ctx)