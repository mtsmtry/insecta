module Rewriter where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Library
import Data

analyzeErrorM:: Message -> Analyzer (Maybe a)
analyzeErrorM msg = Analyzer ([msg], , Nothing)
analyzeErrorB:: Message -> Analyzer Bool
analyzeErrorB msg = Analyzer ([msg], , False)
analyzeError:: Message -> Analyzer ()
analyzeError msg = Analyzer ([msg], , ())

isAssociative:: Rule -> Bool
isAssociative (FuncExpr (_, f) [IdentExpr (_, a), IdentExpr (_, b)], FuncExpr (_, g) [IdentExpr (_, p), IdentExpr (_, q)]) = 
    f == g && a == q && b == p
isAssociative _ = False

isCommutative:: Rule -> Bool
isCommutative (FuncExpr (_, f) [FuncExpr (_, g)[IdentExpr (_, a), IdentExpr (_, b)], IdentExpr (_, c)], 
               FuncExpr (_, h) [IdentExpr (_, x), FuncExpr (_, i)[IdentExpr (_, y), IdentExpr (_, z)]]) = 
    all (==f) [g, h, i] && all (uncurry (==)) [(a, x), (b, y), (c, z)]
isCommutative _ = False

unifyM:: Expr -> Expr -> Analyzer Maybe AssignMap
unifyM p t = do
    ctx <- getContext
    return $ unify (ctxTMap ctx) p t

convertType:: Expr -> Expr -> Analyzer Bool
convertType value trgType = do
    mt <- evalType value
    case mt of
        Just t -> if equas t trgType then return True else do
            pmap <- fmap ctxPred getContext
            pred <- M.lookup (showName trgType) pmap
            masg <- unifyM pred value
            case masg of
                Just{} -> return True
                Nothing -> return False
        Nothing -> return False

unify:: TypeMap -> Expr -> Expr -> Maybe AssignMap
unify tmap p t = if b then Just m else Nothing where
    (b, m) = (runState $ unifym p t) M.empty
    unifym:: Expr -> Expr -> State AssignMap Bool
    unifym Rewrite{} _ = error "Do not use Rewrite in a rule"
    unifym e (Rewrite _ a _) = unifym e a -- use newer
    unifym e@(IdentExpr (_, var)) t = case M.lookup var tmap of
        Just{} -> return $ equals e t -- if pattern is in global scope
        Nothing -> state $ \m-> maybe (True, M.insert var (getLatestExpr t) m) (\x-> (x `equals` t, m)) $ M.lookup var m
    unifym (NumberExpr _ n) (NumberExpr _ n') = return $ n == n'
    unifym NumberExpr{} _ = return False
    unifym (FuncExpr f ax) (FuncExpr f' ax') = (and $ unifym' ax ax') (sameStr f f') where
        and f r = if r then f else return False
        unifym' (e:ex) (e':ex') = unifym e e' >>= and (unifym' ex ex')
        unifym' [] [] = return True
        unifym' _ _ = return False
    unifym FuncExpr{} _ = return False

assign:: M.Map String Expr -> Expr -> Expr
assign m e@(IdentExpr (_, var)) = fromMaybe e $ M.lookup var m
assign m (FuncExpr f as) = FuncExpr f $ map (assign m) as
assign m e = e

-- equals on math semantic
-- ignore code position and rewrite
equals:: Expr -> Expr -> Bool
equals (IdentExpr (_, a)) (IdentExpr (_, b)) = a == b
equals (FuncExpr f as) (FuncExpr g bs) = (sameStr f g) && all (uncurry equals) (zip as bs)
equals (NumberExpr _ n) (NumberExpr _ m) = n == m
equals (StringExpr (_, a)) (StringExpr (_, b)) = a == b
equals Rewrite{} _ = error "Can not use Rewrite"
equals _ Rewrite{} = error "Can not use Rewrite"
equals _ _ = False

addSimp:: Expr -> Expr -> Analyzer ()
addSimp (FuncExpr (_, a) _) (FuncExpr pb@(p, b) _) = do
    m <- fmap ctxSimps getContext
    case (elemIndex a m, elemIndex b m) of
        (Just a', Just b') -> when (a' > b') $ analyzeError $ Message pb "Not as simple as the left side"
        (Just a', Nothing) -> updateSimp $ insertAt b a'
        (Nothing, Just b') -> updateSimp $ insertAt a (b'+1)
        (Nothing, Nothing) -> updateSimp $ (\m-> b:a:m)
    where
    insertAt:: a -> Int -> [a] -> [a]
    insertAt x 0 as = x:as
    insertAt x i (a:as) = a:insertAt x (i - 1) as
addSimp _ (FuncExpr pb@(_, b) _) = do 
    updateSimp $ (\m-> b:m)
    analyzeError $ Message pb "You can not use constants on the left side"
addSimp (FuncExpr (_, a) _) _ = do 
    m <- fmap ctxSimps getContext
    if a `elem` m then return () else updateSimp (a:)
addSimp a _ = analyzeError $ Message (getPosAndStr a) "Constants always have the same simplicity"

-- どれか一つの引数に効果を適用し、同じ順番で引数を返す
-- 適用できる引数がなかったときはNothingを返す
applyArgs:: (Expr -> Maybe Expr) -> [Expr] -> Maybe [Expr]
applyArgs f xs = applyArgs' xs [] where
    applyArgs':: [Expr] -> [Expr] -> Maybe [Expr]
    applyArgs' [] _ = Nothing
    applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

simplify:: Simplicity -> TypeMap -> RuleMap -> Expr -> Expr
simplify smap tmap m e = maybe e (simplify smap tmap m) $ step e where
    getSimp f = fromMaybe (-1) $ elemIndex f smap

    step:: Expr -> Maybe Expr
    step e = applyByHeadList heads e where
        simpCompare a b = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e

    lookupHeads:: Expr -> [(String, Int)]
    lookupHeads (Rewrite _ a _) = lookupHeads a
    lookupHeads (FuncExpr (_, f) as) = (f, getSimp f):concatMap lookupHeads as
    lookupHeads _ = []

    apply:: [Rule] -> Expr -> Maybe Expr
    apply (r@(a, b):rs) e = maybe (apply rs e) (\m-> Just $ Rewrite (StepReason r m) (assign m b) e) (unify tmap a e)
    apply [] e = Nothing
    
    applyAtSimp:: [Rule] -> Int -> Expr -> Maybe Expr
    -- applyAtSimp rs s e@(Rewrite r a b) = case applyAtSimp rs s a of 
    --    Just (Rewrite r' a' b') -> Just $ Rewrite r' a' e
    --    Just e -> Just $ Rewrite r e b
    --    Nothing -> Nothing
    applyAtSimp rs s (Rewrite r a b) = applyAtSimp rs s a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rs s e@(FuncExpr h@(_, f) as) = 
        if s == getSimp f then apply rs e <|> e' else e' where
            e' = applyArgs (applyAtSimp rs s) as >>= Just . FuncExpr h
    applyAtSimp _ _ _ = Nothing
    
    applyByHeadList:: [(String, Int)] -> Expr -> Maybe Expr
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList xs e

-- [A, B, C, X, Y, Z] [P, Q, R, X, Y, Z] => [A, B, C, X, R, Q, P]
-- marge (Z, (Y, (X, (C, (B, A))))) (Z, (Y, (X, (R, (Q, P)))))
-- => marge (Y, (X, (C, (B, A)))) (Y, (X, (R, (Q, P)))) Z
-- => marge (X, (C, (B, A))) (X, (R, (Q, P))) Y
-- => marge (C, (B, A)) (R, (Q, P)) X
-- => (P, (Q, (R, (X, (C, (B, A))))))
mergeRewrite:: Expr -> Expr -> Maybe Expr
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, Expr, Reason) -> Expr -> Expr -> Maybe Expr
    -- A a B b C c X x Y y Z + P p Q q R r X x Y y Z => A a B b C c X r R q Q p P
    -- marge (A a B b C c X x Y y Z) (P p Q q R r X x' Y y' Z) Nothing
    -- => marge (A a B b C c X x Y) (P p Q q R r X x Y) (y, Z, y')
    -- => marge (A a B b C c X) (P p Q q R r X) (x, Y, x')
    -- => marge (A a B b C) (P p Q q R) (c, X, r)
    -- => appendStep (A a B b C c X) (P p Q q R) r
    mergeRewrite junction former@(Rewrite r a b) latter@(Rewrite r' a' b') = if equals a a'
        then mergeRewrite (Just (r, a, r')) b b'
        else case junction of
            Just (jr, je, jr') -> Just $ appendStep jr' (Rewrite jr je former) latter 
            Nothing -> Nothing
    -- marge a [s, t, a] => [a, t, s]
    mergeRewrite _ former latter@(Rewrite r a b) = if equals former a
        then mergeRewrite Nothing former a >>= \x-> Just $ appendStep r x b
        else Nothing
    -- marge [s, t, a] a => [s, t, a]
    mergeRewrite _ former@(Rewrite r a b) latter = if equals a latter
        then mergeRewrite Nothing a latter >>= \x-> Just $ Rewrite r x b
        else Nothing
    -- marge [A, B, f([a, b], u)] [P, Q, f([s, t, b], u)] 
    -- => [A, B, marge f([a, b], u) f([s, t, b], u), Q, P]
    -- => [A, B, f(marge [a, b] [s, t, b], marge u u), Q, P]
    -- => [A, B, f([a, b, t, s],  u), Q, P]
    mergeRewrite _ (FuncExpr f as) (FuncExpr g bs) = if sameStr f g
        then FuncExpr f <$> conjMaybe (zipWith (mergeRewrite Nothing) as bs)
        else Nothing
    -- marge x x => x 
    mergeRewrite _ a b = if equals a b then Just a else Nothing

    -- [A, B, X] X => [A, B, X]
    -- [A, B, X] Y => Nothing
    appendStep:: Reason -> Expr -> Expr -> Expr
    appendStep r' t (Rewrite r a b) = Rewrite r a (appendStep r' t b)
    appendStep r t u = Rewrite r u t

type Derivater = (Expr, Expr) -> Maybe Expr

derivate:: RuleMap -> TypeMap -> (Expr, Expr) -> Maybe Expr
derivate m tmap = applyDiff derivateByRuleList where
    applyDiff:: Derivater -> (Expr, Expr) -> Maybe Expr
    applyDiff d pair@(FuncExpr f as, FuncExpr g bs) = if sameStr f g && length as == length bs
        then case num of
            0 -> Nothing
            1 -> derivate m tmap x >>= \t-> Just $ FuncExpr f (map snd xs' ++ t:map snd xs) where
                (xs', x:xs) = splitAt idx args
            _ -> d pair
        else d pair where
            args = zip as bs
            es = fmap (uncurry equals) args
            (idx, num) = encount False es
            -- (element, list) -> (index of the first encountered element, number of encounters)
            encount:: Eq a => a -> [a] -> (Int, Int)
            encount = encount' (-1, 0) where
                encount':: Eq a => (Int, Int) -> a -> [a] -> (Int, Int)
                encount' (i, n) e (x:xs) = encount' (if n > 0 then i else i + 1, if e == x then n + 1 else n) e xs
                encount' p _ [] = p
    applyDiff d pair = d pair

    derivateByRuleList::Derivater
    derivateByRuleList pair@(FuncExpr (_, h) as, goal) = M.lookup h m 
        >>= foldr ((<|>) . flip derivateByRule pair) Nothing
    derivateByRuleList _ = Nothing

    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' r@(ra, rb) (ta, tb) = unify tmap ra ta >>= \m-> if assign m rb `equals` tb 
            then Just $ Rewrite (ImplReason r m) tb ta
            else Nothing

getLatestExpr:: Expr -> Expr
getLatestExpr (Rewrite _ a _) = getLatestExpr a
getLatestExpr e = e 

getOldestExpr:: Expr -> Expr
getOldestExpr (Rewrite _ _ b) = getOldestExpr b
getOldestExpr e = e

getExprPos:: Expr -> Position
getExprPos (StringExpr (p, _)) = p
getExprPos (IdentExpr (p, _)) = p
getExprPos (NumberExpr p _) = p
getExprPos (FuncExpr (p, _) _) = p

extractMaybe:: [Maybe a] -> [a]
extractMaybe [] = []
extractMaybe (x:xs) = maybe (extractMaybe xs) (:extractMaybe xs) x