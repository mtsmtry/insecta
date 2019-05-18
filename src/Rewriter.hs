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

extractRewrite:: Expr -> Expr
extractRewrite (Rewrite _ a _) = extractRewrite a
extractRewrite (FuncExpr h as) = FuncExpr h $ map extractRewrite as
extractRewrite x = x

unify:: Expr -> Expr -> Maybe (M.Map String Expr)
unify p t = if b then Just m else Nothing where
    (b, m) = (runState $ unifym p t) M.empty
    unifym:: Expr -> Expr -> State (M.Map String Expr) Bool
    unifym Rewrite{} _ = error "Do not use Rewrite in a rule"
    unifym e (Rewrite _ a _) = unifym e a -- use newer
    unifym (IdentExpr (_, var)) t = state $ \m-> maybe (True, M.insert var (extractRewrite t) m) (\x-> (x `equals` t, m)) $ M.lookup var m
    unifym (NumberExpr _ n) (NumberExpr _ n') = return $ n == n'
    unifym NumberExpr{} _ = return False
    unifym (FuncExpr f ax) (FuncExpr f' ax') = (and $ unifym' ax ax') (showHead f == showHead f') where
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
equals (FuncExpr f as) (FuncExpr g bs) = (showHead f == showHead g) && all (uncurry equals) (zip as bs)
equals (NumberExpr _ n) (NumberExpr _ m) = n == m
equals (StringExpr (_, a)) (StringExpr (_, b)) = a == b
equals Rewrite{} _ = error "Can not use Rewrite"
equals _ Rewrite{} = error "Can not use Rewrite"
equals _ _ = False

-- functions order by simplicity
type Simplicity = [String]

addSimp:: Simplicity -> Expr -> Expr -> Writer [Message] Simplicity
addSimp m (FuncExpr (PureExprHead (_, a)) _) (FuncExpr (PureExprHead pb@(p, b)) _) = case (elemIndex a m, elemIndex b m) of
    (Just a', Just b') -> if a' > b' then writer (m, [Message pb "Not as simple as the left side"]) else return m
    (Just a', Nothing) -> return $ insertAt b a' m
    (Nothing, Just b') -> return $ insertAt a (b'+1) m
    (Nothing, Nothing) -> return $ b:a:m
    where
    insertAt:: a -> Int -> [a] -> [a]
    insertAt x 0 as = x:as
    insertAt x i (a:as) = a:insertAt x (i - 1) as
addSimp m FuncExpr{} FuncExpr{} = error "Not PureExprHead"
addSimp m _ (FuncExpr (PureExprHead pb) _) = writer ([], [Message pb "You can not use constants on the left side"])
addSimp m (FuncExpr (PureExprHead pa) _) _ = return m
addSimp m a _ = writer ([], [Message (getPosAndStr a) "Constants always have the same simplicity"]) 

appSimp :: Simplicity -> Expr -> Expr
appSimp m (FuncExpr h as) = FuncExpr h' $ map (appSimp m) as where
    h' = case h of PureExprHead pt@(_, t) -> ExprHead pt $ fromMaybe 0 $ elemIndex t m; _-> h
appSimp _ e = e

-- どれか一つの引数に効果を適用し、同じ順番で引数を返す
-- 適用できる引数がなかったときはNothingを返す
applyArgs:: (Expr -> Maybe Expr) -> [Expr] -> Maybe [Expr]
applyArgs f xs = applyArgs' xs [] where
    applyArgs':: [Expr] -> [Expr] -> Maybe [Expr]
    applyArgs' [] _ = Nothing
    applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

type RuleMap = M.Map String [Rule]

simplify:: RuleMap -> Expr -> Expr
simplify m e = maybe e (simplify m) $ step m e where
    step:: RuleMap -> Expr -> Maybe Expr
    step m e = applyByHeadList m heads e where
        simpCompare (ExprHead _ a) (ExprHead _ b) = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e

    lookupHeads:: Expr -> [ExprHead]
    lookupHeads x = lookupHeads' $ extractRewrite x where
        lookupHeads' (FuncExpr h as) = h:concatMap lookupHeads' as
        lookupHeads' _ = []

    apply:: [Rule] -> Expr -> Maybe Expr
    apply (r@(a, b):rs) e = maybe (apply rs e) (\m-> Just $ Rewrite r (assign m b) e) (unify a e)
    apply [] e = Nothing
    
    applyAtSimp:: [Rule] -> Int -> Expr -> Maybe Expr
    applyAtSimp rs s (Rewrite r a b) = applyAtSimp rs s a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rs s e@(FuncExpr h@(ExprHead (_, t) s') as) = 
        if s == s' then apply rs e <|> e' else e' where
            e' = applyArgs (applyAtSimp rs s) as >>= Just . FuncExpr h
    applyAtSimp _ _ _ = Nothing
    
    applyByHeadList:: RuleMap -> [ExprHead] -> Expr -> Maybe Expr
    applyByHeadList _ [] _ = Nothing
    applyByHeadList m (ExprHead (_, f) s:xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList m xs e

type Derivater = (Expr, Expr) -> Maybe Expr

derivate:: RuleMap -> (Expr, Expr) -> Maybe Expr
derivate m = applyDiff derivateByRuleList where
    applyDiff:: Derivater -> (Expr, Expr) -> Maybe Expr
    applyDiff d pair@(FuncExpr f as, FuncExpr g bs) = if showHead f == showHead g && length as == length bs
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
    derivateByRuleList pair@(FuncExpr h as, goal) = M.lookup (showHead h) m 
        >>= foldr ((<|>) . (flip derivateByRule) pair) Nothing
    derivateByRuleList _ = Nothing
    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' r@(ra, rb) (ta, tb) = unify ra ta >>= \m-> if assign m rb `equals` tb 
            then Just $ Rewrite r ta tb
            else Nothing

showSteps:: Expr -> [String]
showSteps x = map showExprOldest $ reverse $ showSteps' [x] x where
    showSteps':: [Expr] -> Expr -> [Expr]
    showSteps' p e = maybe p (\x-> showSteps' (x:p) x) $ nextStep e

    nextStep:: Expr -> Maybe Expr
    nextStep (Rewrite r a b) = Just $ maybe a (Rewrite r a) $ nextStep b
    nextStep (FuncExpr h as) = applyArgs nextStep as >>= Just . FuncExpr h
    nextStep _ = Nothing

showFuncExpr:: (Expr -> String) -> ExprHead -> [Expr] -> String
showFuncExpr fshow h as = if isAlpha (head f) || length as /= 2 
    then f ++ "(" ++ intercalate "," (map fshow as) ++ ")"
    else let [a, b] = as in fshow a ++ f ++ fshow b where f = showHead h

showExpr:: Expr -> String
showExpr (Rewrite _ a b) = error "Can not use Rewrite"
showExpr (StringExpr (_, s)) = "\"" ++ s ++ "\"" 
showExpr (IdentExpr (_, x)) = x
showExpr (NumberExpr _ n) = show n 

showExprOldest:: Expr -> String
showExprOldest (Rewrite _ a b) = showExprOldest b
showExprOldest (FuncExpr h as) = showFuncExpr showExprOldest h as
showExprOldest e = showExpr e

showExprLatest:: Expr -> String
showExprLatest (Rewrite _ a b) = showExprLatest a
showExprLatest (FuncExpr h as) = showFuncExpr showExprLatest h as
showExprLatest e = showExpr e

showExprAsRewrites:: Expr -> String
showExprAsRewrites e@Rewrite{} = "[" ++ intercalate "," steps ++ "]" where
    steps = map showExprAsRewrites $ expandRewrite e
    expandRewrite:: Expr -> [Expr]
    expandRewrite (Rewrite _ a b) = expandRewrite b ++ expandRewrite a
    expandRewrite e = [e]
showExprAsRewrites (FuncExpr h as) = showFuncExpr showExprAsRewrites h as
showExprAsRewrites e = showExpr e

getHeadStr:: ExprHead -> PosStr
getHeadStr (ExprHead ps _) = ps
getHeadStr (PureExprHead ps) = ps

getExprPos:: Expr -> Position
getExprPos (StringExpr (p, _)) = p
getExprPos (IdentExpr (p, _)) = p
getExprPos (NumberExpr p _) = p
getExprPos (FuncExpr h _) = fst $ getHeadStr h

showCodeExpr:: Expr -> PosStr
showCodeExpr e = (getExprPos e, showExprOldest e)

extractMaybe:: [Maybe a] -> [a]
extractMaybe [] = []
extractMaybe (x:xs) = maybe (extractMaybe xs) (:extractMaybe xs) x