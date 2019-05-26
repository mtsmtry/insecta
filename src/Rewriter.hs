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

isAssociative:: Rule -> Bool
isAssociative (FuncExpr f [IdentExpr a, IdentExpr b], FuncExpr g [IdentExpr p, IdentExpr q]) = 
    f == g && a == q && b == p
isAssociative _ = False

isCommutative:: Rule -> Bool
isCommutative (FuncExpr f [FuncExpr g [IdentExpr a, IdentExpr b], IdentExpr c], 
               FuncExpr h [IdentExpr x, FuncExpr i [IdentExpr y, IdentExpr z]]) = 
    all (==f) [g, h, i] && all (uncurry (==)) [(a, x), (b, y), (c, z)]
isCommutative _ = False

evalType:: Expr -> Expr
evalType StringExpr{} = makeIdentExpr "Char"
evalType NumberExpr{} = makeIdentExpr "N"
evalType (IdentExpr (EntityIdent _ ent)) = texpr ent
evalType (FuncExpr (EntityIdent _ ent) _) = texpr ent
evalType (Rewrite _ newer _) = evalType newer

unify:: Expr -> Expr -> Maybe AssignMap
unify p t = if b then Just m else Nothing where
    (b, m) = (runState $ unifym p t) M.empty
    unifym:: Expr -> Expr -> State AssignMap Bool
    unifym Rewrite{} _ = error "Do not use Rewrite in a rule"
    unifym e (Rewrite _ a _) = unifym e a -- use newer
    unifym e@(IdentExpr (EntityIdent _ ent)) t = if isGlb ent 
        then return $ equals e t -- if pattern is in global scope
        else case M.lookup (name ent) m of
            Just x -> state (equals x t, )
            Nothing -> state $ (True, ) . M.insert (name ent) (getLatestExpr t)
    unifym (NumberExpr _ n) (NumberExpr _ n') = return $ n == n'
    unifym NumberExpr{} _ = return False
    unifym (FuncExpr f ax) (FuncExpr f' ax') = (and $ unifym' ax ax') (f == f') where
        and f r = if r then f else return False
        unifym' (e:ex) (e':ex') = unifym e e' >>= and (unifym' ex ex')
        unifym' [] [] = return True
        unifym' _ _ = return False
    unifym FuncExpr{} _ = return False

assign:: M.Map String Expr -> Expr -> Expr
assign m e@(IdentExpr var) = fromMaybe e $ M.lookup (show var) m
assign m (FuncExpr f as) = FuncExpr f $ map (assign m) as
assign m e = e

equals:: Expr -> Expr -> Bool
equals (IdentExpr a) (IdentExpr b) = a == b
equals (FuncExpr f as) (FuncExpr g bs) = (f == g) && all (uncurry equals) (zip as bs)
equals (NumberExpr _ n) (NumberExpr _ m) = n == m
equals (StringExpr a) (StringExpr b) = a == b
equals Rewrite{} _ = error "Can not use Rewrite"
equals _ Rewrite{} = error "Can not use Rewrite"
equals _ _ = False

addSimp:: Expr -> Expr -> Analyzer ()
addSimp (FuncExpr f _) (FuncExpr g _) = do
    m <- fmap ctxSimps getContext
    let (fn, gn) = (show f, show g)
    case (elemIndex fn m, elemIndex gn m) of
        (Just fi, Just gi) -> when (fi > gi) $ analyzeError g "Not as simple as the left side"
        (Just fi, Nothing) -> updateSimp $ insertAt gn fi
        (Nothing, Just gi) -> updateSimp $ insertAt fn (gi+1)
        (Nothing, Nothing) -> updateSimp $ (\m-> gn:fn:m)
    where
    insertAt:: a -> Int -> [a] -> [a]
    insertAt x 0 as = x:as
    insertAt x i (a:as) = a:insertAt x (i - 1) as
addSimp _ (FuncExpr g _) = do 
    updateSimp $ (\m-> (show g):m)
    analyzeError g "You can not use constants on the left side"
addSimp (FuncExpr f _) _ = do 
    m <- fmap ctxSimps getContext
    let fn = show f
    if fn `elem` m then return () else updateSimp (fn:)
addSimp f _ = analyzeError (showIdent f) "Constants always have the same simplicity"

-- どれか一つの引数に効果を適用し、同じ順番で引数を返す
-- 適用できる引数がなかったときはNothingを返す
applyArgs:: (Expr -> Maybe Expr) -> [Expr] -> Maybe [Expr]
applyArgs f xs = applyArgs' xs [] where
    applyArgs':: [Expr] -> [Expr] -> Maybe [Expr]
    applyArgs' [] _ = Nothing
    applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

simplify:: RuleMap -> Expr -> Expr
simplify m e = maybe e (simplify m) $ step e where
    step:: Expr -> Maybe Expr
    step e = applyByHeadList heads e where
        simpCompare a b = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e
    lookupHeads:: Expr -> [(String, Int)]
    lookupHeads (Rewrite _ a _) = lookupHeads a
    lookupHeads (FuncExpr f as) = (show f, (simp . getEnt) f):concatMap lookupHeads as
    lookupHeads _ = []
    apply:: [Rule] -> Expr -> Maybe Expr
    apply (r@(a, b):rs) e = maybe (apply rs e) (\m-> Just $ Rewrite (StepReason r m) (assign m b) e) (unify a e)
    apply [] e = Nothing
    applyAtSimp:: [Rule] -> Int -> Expr -> Maybe Expr
    applyAtSimp rs s (Rewrite r a b) = applyAtSimp rs s a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rs s e@(FuncExpr h as) = 
        if s == (simp . getEnt) h then apply rs e <|> e' else e' where
            e' = applyArgs (applyAtSimp rs s) as >>= Just . FuncExpr h
    applyAtSimp _ _ _ = Nothing
    applyByHeadList:: [(String, Int)] -> Expr -> Maybe Expr
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList xs e

mergeRewrite:: Expr -> Expr -> Maybe Expr
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, Expr, Reason) -> Expr -> Expr -> Maybe Expr
    mergeRewrite junction former@(Rewrite r a b) latter@(Rewrite r' a' b') = if equals a a'
        then mergeRewrite (Just (r, a, r')) b b'
        else case junction of
            Just (jr, je, jr') -> Just $ appendStep jr' (Rewrite jr je former) latter 
            Nothing -> Nothing
    mergeRewrite _ former latter@(Rewrite r a b) = if equals former a
        then mergeRewrite Nothing former a >>= \x-> Just $ appendStep r x b
        else Nothing
    mergeRewrite _ former@(Rewrite r a b) latter = if equals a latter
        then mergeRewrite Nothing a latter >>= \x-> Just $ Rewrite r x b
        else Nothing
    mergeRewrite _ (FuncExpr f as) (FuncExpr g bs) = if f == g
        then FuncExpr f <$> conjMaybe (zipWith (mergeRewrite Nothing) as bs)
        else Nothing
    mergeRewrite _ a b = if equals a b then Just a else Nothing
    appendStep:: Reason -> Expr -> Expr -> Expr
    appendStep r' t (Rewrite r a b) = Rewrite r a (appendStep r' t b)
    appendStep r t u = Rewrite r u t

type Derivater = (Expr, Expr) -> Maybe Expr
derivate:: RuleMap -> (Expr, Expr) -> Maybe Expr
derivate m = applyDiff derivateByRuleList where
    applyDiff:: Derivater -> (Expr, Expr) -> Maybe Expr
    applyDiff d pair@(FuncExpr f as, FuncExpr g bs) = if f == g && length as == length bs
        then case num of
            0 -> Nothing
            1 -> derivate m x >>= \t-> Just $ FuncExpr f (map snd xs' ++ t:map snd xs) where
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

    derivateByRuleList:: Derivater
    derivateByRuleList pair@(FuncExpr h as, goal) = M.lookup (show h) m 
        >>= foldr ((<|>) . flip derivateByRule pair) Nothing
    derivateByRuleList _ = Nothing

    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' r@(ra, rb) (ta, tb) = unify ra ta >>= \m-> if assign m rb `equals` tb 
            then Just $ Rewrite (ImplReason r m) tb ta
            else Nothing

getLatestExpr:: Expr -> Expr
getLatestExpr (Rewrite _ a _) = getLatestExpr a
getLatestExpr e = e 

getOldestExpr:: Expr -> Expr
getOldestExpr (Rewrite _ _ b) = getOldestExpr b
getOldestExpr e = e

extractMaybe:: [Maybe a] -> [a]
extractMaybe [] = []
extractMaybe (x:xs) = maybe (extractMaybe xs) (:extractMaybe xs) x