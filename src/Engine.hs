module Engine where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Parse

showToken:: Token -> String
showToken (Symbol s) = s
showToken (Ident s) = s

showHead:: ExprHead -> String
showHead (ExprHead t _) = showToken t
showHead (PureExprHead t) = showToken t

makeRules:: [Expr] -> ([Rule], [Rule])
makeRules [] = ([], [])
makeRules (x:xs) = if isStep then (r:ms, mi) else (ms, r:mi) where 
    (isStep, r) = makeRule x
    (ms, mi) = makeRules xs
    -- expression -> (is step rule, rule)
    makeRule:: Expr -> (Bool, Rule)
    makeRule (FuncExpr (PureExprHead (Symbol kind)) [a, b]) = case kind of
        ">>=" -> (True, (a, b))
        "->" -> (False, (a, b))
        f -> error f

type RuleMap = M.Map String [Rule] 
toRuleMap:: [Rule] -> RuleMap
toRuleMap rs = toRuleMap' M.empty $ groupBy equalsHead rs where
    equalsHead (FuncExpr h _, _) (FuncExpr h' _, _) = showHead h == showHead h'
    getHead:: [Rule] -> String
    getHead ((FuncExpr h _, _):_) = showHead h
    toRuleMap':: RuleMap -> [[Rule]] -> RuleMap
    toRuleMap' = foldl (\m r-> M.insert (getHead r) r m)

type Simplicity = [String]
makeSimp:: Simplicity -> [Rule] -> Simplicity
makeSimp m [] = m
makeSimp m ((a, b):rs) = makeSimp (addSimp m a b) rs where
    addSimp:: Simplicity -> Expr -> Expr -> Simplicity
    addSimp m (FuncExpr a _) (FuncExpr b _) = addSimp' m (showHead a) (showHead b) where
        addSimp':: Simplicity -> String -> String -> Simplicity
        addSimp' m a b = case (elemIndex a m, elemIndex b m) of
            (Just a', Just b') -> if a' > b' then error "error" else m
            (Just a', Nothing) -> insertAt b a' m
            (Nothing, Just b') -> insertAt a (b'+1) m
            (Nothing, Nothing) -> b:a:m
    addSimp m _ _ = m
    insertAt:: a -> Int -> [a] -> [a]
    insertAt x 0 as = x:as
    insertAt x i (a:as) = a:insertAt x (i - 1) as

makeRuleMap:: [Expr] -> (RuleMap, RuleMap, Simplicity)
makeRuleMap xs = (toMap a, toMap b, simp) where 
    toAppSimp (a, b) = (appSimp simp a, appSimp simp b)
    toMap = toRuleMap . map toAppSimp
    (a, b) = makeRules xs
    simp = makeSimp [] a

extractRewrite:: Expr -> Expr
extractRewrite (Rewrite _ a _) = extractRewrite a
extractRewrite (FuncExpr h as) = FuncExpr h $ map extractRewrite as
extractRewrite x = x

unify:: Expr -> Expr -> Maybe (M.Map String Expr)
unify p t = if b then Just m else Nothing where
    (b, m) = (runState $ unifym p t) M.empty
    unifym:: Expr -> Expr -> State (M.Map String Expr) Bool
    unifym Rewrite{} _ = error "Do not use Rewrite in a rule"
    unifym e (Rewrite _ a _) = unifym e a
    unifym (IdentExpr var) t = state $ \m-> maybe (True, M.insert var (extractRewrite t) m) (\x-> (x==t, m)) $ M.lookup var m
    unifym (NumberExpr n) (NumberExpr n') = return $ n == n'
    unifym (NumberExpr _) _ = return False
    unifym (FuncExpr f ax) (FuncExpr f' ax') = (and $ unifym' ax ax') (showHead f == showHead f') where
        and f r = if r then f else return False
        unifym' (e:ex) (e':ex') = unifym e e' >>= and (unifym' ex ex')
        unifym' [] [] = return True
        unifym' _ _ = return False
    unifym FuncExpr{} _ = return False

assign:: M.Map String Expr -> Expr -> Expr
assign m e@(IdentExpr var) = fromMaybe e $ M.lookup var m
assign m (FuncExpr f as) = FuncExpr f $ map (assign m) as
assign m e = e

equals:: (Expr, Expr) -> Bool
equals (a, b) = extractRewrite a == extractRewrite b

applyDiff:: Derivater -> (Expr, Expr) -> Maybe Expr
applyDiff d pair@(FuncExpr f as, FuncExpr g bs) = if f == g 
    then case num of
        0 -> Nothing
        1 -> maybe Nothing makeExpr $ applyDiff d x where
            (xs', x:xs) = splitAt idx args
            makeExpr t = Just $ FuncExpr f ((map fst xs') ++ t:(map fst xs))
        _ -> d pair
    else d pair where 
        args = zip as bs
        es = fmap equals $ args
        (idx, num) = encount True es
        -- (element, list) -> (index of the first encountered element, number of encounters)
        encount:: Eq a => a -> [a] -> (Int, Int)
        encount = encount' (-1, 0) where
            encount' p _ [] = p
            encount' (i, n) e (x:xs) = encount' (if n > 0 then i else i + 1, if e == x then n + 1 else n) e xs

type Derivater = (Expr, Expr) -> Maybe Expr
derviateDiff:: Rule -> Derivater
derviateDiff d = applyDiff $ derviate d where
    derviate:: Rule -> Derivater
    derviate (a, b) (ea, eb) = unify a ea >>= \m-> unify b eb >>= const (Just $ assign m eb)

appSimp :: Simplicity -> Expr -> Expr
appSimp m (FuncExpr h as) = FuncExpr h' $ map (appSimp m) as where
    h' = case h of PureExprHead t -> ExprHead t $ fromMaybe 0 $ elemIndex (showToken t) m; _-> h
appSimp _ e = e

applyArgs:: (Expr -> Maybe Expr) -> [Expr] -> Maybe [Expr]
applyArgs f xs = applyArgs' xs [] where
    applyArgs':: [Expr] -> [Expr] -> Maybe [Expr]
    applyArgs' [] _ = Nothing
    applyArgs' (a:as) as' = maybe (applyArgs' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

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
    applyAtSimp rs s e@(FuncExpr h@(ExprHead t s') as) = 
        if s == s' then apply rs e <|> e' else e' where
            e' = applyArgs (applyAtSimp rs s) as >>= Just . FuncExpr h
    applyAtSimp _ _ _ = Nothing
    
    applyByHeadList:: RuleMap -> [ExprHead] -> Expr -> Maybe Expr
    applyByHeadList _ [] _ = Nothing
    applyByHeadList m (ExprHead f s:xs) e = (M.lookup (showToken f) m >>= \x-> applyAtSimp x s e) <|> applyByHeadList m xs e

showSteps:: Expr -> [Expr]
showSteps x = showSteps' [x] x where
    showSteps':: [Expr] -> Expr -> [Expr]
    showSteps' p e = maybe p (\x-> showSteps' (x:p) x) $ nextStep e

    nextStep:: Expr -> Maybe Expr
    nextStep (Rewrite _ a b) = Just a
    nextStep (FuncExpr h as) = applyArgs nextStep as >>= Just . FuncExpr h
    nextStep _ = Nothing

showExpr:: Expr -> String
showExpr (Rewrite _ a b) = showExpr b
showExpr (StringExpr s) = "\"" ++ s ++ "\"" 
showExpr (IdentExpr x) = x
showExpr (NumberExpr n) = show n
showExpr (FuncExpr h as) = if isAlpha (head f) || length as /= 2 
    then f ++ "(" ++ intercalate "," (map showExpr as) ++ ")"
    else let [a, b] = as in showExpr a ++ f ++ showExpr b where f = showHead h
 
extractMaybe:: [Maybe a] -> [a]
extractMaybe [] = []
extractMaybe (x:xs) = maybe (extractMaybe xs) (:extractMaybe xs) x