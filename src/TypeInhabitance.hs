module TypeInhabitance where

type Symb = String

infixr 3 :->

data Type = TVar Symb      -- типовый атом
          | Type :-> Type  -- стрелочный тип
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизирована
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord)

uncurry2List :: Type -> (Symb,[Type])
uncurry2List (TVar v) = (v, [])
uncurry2List (u :-> v) = let (symb, types) = uncurry2List v in (symb, u:types)

uncurry2RevList  :: Type -> (Symb,[Type])
uncurry2RevList (TVar v) = (v, [])
uncurry2RevList t = let (symb, types) = uncurry2List t in (symb, reverse types)

unMeta :: Ctx -> TNF -> [TNF]
unMeta ctx (Meta t) = expand ctx t
unMeta ctx (TNF abs index tails) = do
    let newCtx = abs ++ ctx
    newTails <- traverse (unMeta newCtx) tails
    pure (TNF abs index newTails)

expand :: Ctx -> Type -> [TNF]
expand ctx (TVar varType) = do
    (t, i) <- zip ctx [0..]
    suitableArgs <- [argTypes | let (retType, argTypes) = uncurry2List t, retType == varType]
    pure (TNF [] i (Meta <$> suitableArgs))
expand ctx t@(u :-> v) = do
    let (retType, argTypes) = uncurry2RevList t
    TNF [] i tails <- expand (argTypes ++ ctx) (TVar retType)
    pure (TNF argTypes i tails)

isTerm :: TNF -> Bool
isTerm (Meta _) = False
isTerm (TNF _ _ tails) = all isTerm tails

allTNFGens :: Type -> [[TNF]]
allTNFGens tau = takeWhile (not . null) (iterate go [Meta tau])
  where
    go :: [TNF] -> [TNF]
    go tnfs | all isTerm tnfs = []
    go tnfs = concat (unMeta [] <$> filter (not . isTerm) tnfs)

inhabGens :: Type -> [[TNF]]
inhabGens tau = [filter isTerm nfs | nfs <- allTNFGens tau]

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens