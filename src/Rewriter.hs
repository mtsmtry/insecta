module Rewriter where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Parser
import Library

unify:: Expr -> Expr -> Maybe AssignMap
unify p t = if b then Just m else Nothing where
    (b, m) = (runState $ unifym p t) M.empty
    unifym:: Expr -> Expr -> State AssignMap Bool
    unifym Rewrite{} _ = error "Do not use Rewrite in a rule"
    unifym e (Rewrite _ a _) = unifym e a -- use newer
    unifym (IdentExpr (_, var)) t = state $ \m-> maybe (True, M.insert var (getLatestExpr t) m) (\x-> (x `equals` t, m)) $ M.lookup var m
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

-- functions order by simplicity
type Simplicity = [String]

addSimp:: Simplicity -> Expr -> Expr -> Writer [Message] Simplicity
addSimp m (FuncExpr (_, a) _) (FuncExpr pb@(p, b) _) = case (elemIndex a m, elemIndex b m) of
    (Just a', Just b') -> if a' > b' then writer (m, [Message pb "Not as simple as the left side"]) else return m
    (Just a', Nothing) -> return $ insertAt b a' m
    (Nothing, Just b') -> return $ insertAt a (b'+1) m
    (Nothing, Nothing) -> return $ b:a:m
    where
    insertAt:: a -> Int -> [a] -> [a]
    insertAt x 0 as = x:as
    insertAt x i (a:as) = a:insertAt x (i - 1) as
addSimp m _ (FuncExpr pb _) = writer ([], [Message pb "You can not use constants on the left side"])
addSimp m (FuncExpr pa _) _ = return m
addSimp m a _ = writer ([], [Message (getPosAndStr a) "Constants always have the same simplicity"]) 

-- どれか一つの引数に効果を適用し、同じ順番で引数を返す
-- 適用できる引数がなかったときはNothingを返す
applyArgs:: (Expr -> Maybe Expr) -> [Expr] -> Maybe [Expr]
applyArgs f xs = applyArgs' xs [] where
    applyArgs':: [Expr] -> [Expr] -> Maybe [Expr]
    applyArgs' [] _ = Nothing
    applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

type RuleMap = M.Map String [Rule]

simplify:: Simplicity -> RuleMap -> Expr -> Expr
simplify smap m e = maybe e (simplify smap m) $ step m e where
    getSimp f = fromMaybe (error "Not in list") $ elemIndex f smap

    step:: RuleMap -> Expr -> Maybe Expr
    step m e = applyByHeadList m heads e where
        simpCompare a b = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e

    lookupHeads:: Expr -> [(String, Int)]
    lookupHeads = lookupHeads' . getLatestExpr where
        lookupHeads' (FuncExpr (_, f) as) = (f, getSimp f):concatMap lookupHeads' as
        lookupHeads' _ = []

    apply:: [Rule] -> Expr -> Maybe Expr
    apply (r@(a, b):rs) e = maybe (apply rs e) (\m-> Just $ Rewrite (StepReason r m) (assign m b) e) (unify a e)
    apply [] e = Nothing
    
    applyAtSimp:: [Rule] -> Int -> Expr -> Maybe Expr
    applyAtSimp rs s (Rewrite r a b) = applyAtSimp rs s a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rs s e@(FuncExpr h@(_, f) as) = 
        if s == getSimp f then apply rs e <|> e' else e' where
            e' = applyArgs (applyAtSimp rs s) as >>= Just . FuncExpr h
    applyAtSimp _ _ _ = Nothing
    
    applyByHeadList:: RuleMap -> [(String, Int)] -> Expr -> Maybe Expr
    applyByHeadList _ [] _ = Nothing
    applyByHeadList m ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList m xs e

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

derivate:: RuleMap -> (Expr, Expr) -> Maybe Expr
derivate m = applyDiff derivateByRuleList where
    applyDiff:: Derivater -> (Expr, Expr) -> Maybe Expr
    applyDiff d pair@(FuncExpr f as, FuncExpr g bs) = if sameStr f g && length as == length bs
        then case num of
            0 -> Nothing-- if length as == 1 then d (head as, head bs) else Nothing
            1 -> d x >>= \t-> Just $ FuncExpr f (map snd xs' ++ t:map snd xs) where
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
        >>= foldr ((<|>) . (flip derivateByRule) pair) Nothing
    derivateByRuleList _ = Nothing
    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' r@(ra, rb) (ta, tb) = unify ra ta >>= \m-> if assign m rb `equals` tb 
            then Just $ Rewrite (ImplReason r m) ta tb
            else Nothing

getLatestExpr:: Expr -> Expr
getLatestExpr (Rewrite _ a _) = a
getLatestExpr e = e 

getOldestExpr:: Expr -> Expr
getOldestExpr (Rewrite _ _ b) = b
getOldestExpr e = e 

showLatestExpr = showExpr . getLatestExpr
showOldestExpr = showExpr . getOldestExpr

showSteps:: Expr -> [String]
showSteps x = map show $ reverse $ showSteps' [(Nothing, x)] x where
    show::(Maybe Reason, Expr) -> String
    show (r, e) = showOldestExpr e ++ " " ++ maybe "" showReason r

    showSteps':: [(Maybe Reason, Expr)] -> Expr -> [(Maybe Reason, Expr)]
    showSteps' p e = maybe p (\x@(_, t)-> showSteps' (x:p) t) $ nextStep e

    showReason:: Reason -> String
    showReason (StepReason (a, b) asg) = showExpr a ++ " >>= " ++ showExpr b ++ " " ++ toJson asg
    showReason (ImplReason (a, b) asg) = showExpr a ++ " -> " ++ showExpr b ++ " " ++ toJson asg
    showReason EqualReason = ""

    nextStep:: Expr -> Maybe (Maybe Reason, Expr)
    nextStep (Rewrite r a b) = Just $ maybe (Just r, a) (\(r', e)-> (r', Rewrite r a e)) $ nextStep b
    nextStep (FuncExpr h as) = applyArgs nextStep as >>= (\(r, as')-> Just (r, FuncExpr h as'))
    nextStep _ = Nothing

    applyArgs:: (Expr -> Maybe (Maybe Reason, Expr)) -> [Expr] -> Maybe (Maybe Reason, [Expr])
    applyArgs f xs = applyArgs' xs [] where
        applyArgs':: [Expr] -> [Expr] -> Maybe (Maybe Reason, [Expr])
        applyArgs' [] _ = Nothing
        applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\(r, e)-> Just (r, reverse (x:as') ++ as)) (f a)

showFuncExpr:: (Expr -> String) -> PosStr -> [Expr]-> String
showFuncExpr fshow (_, "tuple") as = "(" ++ intercalate ", " (map fshow as) ++ ")"
showFuncExpr fshow (_, f) as = if isAlpha (head f) || length as /= 2 
    then f ++ "(" ++ intercalate ", " (map fshow as) ++ ")"
    else let [a, b] = as in fshow a ++ f ++ fshow b 

showExpr:: Expr -> String
showExpr (Rewrite _ a b) = error "Can not use Rewrite"
showExpr (StringExpr (_, s)) = "\"" ++ s ++ "\"" 
showExpr (IdentExpr (_, x)) = x
showExpr (NumberExpr _ n) = show n
showExpr (FuncExpr f as) = showFuncExpr showExpr f as

showExprAsRewrites:: Expr -> String
showExprAsRewrites e@Rewrite{} = "[" ++ intercalate ", " steps ++ "]" where
    steps = map showExprAsRewrites $ expandRewrite e
    expandRewrite:: Expr -> [Expr]
    expandRewrite (Rewrite e a b) = expandRewrite b ++ expandRewrite a
    expandRewrite e = [e]
showExprAsRewrites (FuncExpr h as) = showFuncExpr showExprAsRewrites h as
showExprAsRewrites e = showExpr e

getExprPos:: Expr -> Position
getExprPos (StringExpr (p, _)) = p
getExprPos (IdentExpr (p, _)) = p
getExprPos (NumberExpr p _) = p
getExprPos (FuncExpr (p, _) _) = p

showCodeExpr:: Expr -> PosStr
showCodeExpr e = (getExprPos e, showOldestExpr e)

extractMaybe:: [Maybe a] -> [a]
extractMaybe [] = []
extractMaybe (x:xs) = maybe (extractMaybe xs) (:extractMaybe xs) x