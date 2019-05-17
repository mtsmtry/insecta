module Type where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Parse
import Engine

type TypeMap = M.Map String Expr

evalType:: TypeMap -> Expr -> Writer [Message] (Maybe Expr)
evalType tmap (IdentExpr ph@(_, h)) =  maybe (writer (Nothing, [Message ph "Not defined"])) (return . Just) (M.lookup h tmap)
evalType tmap (FuncExpr (PureExprHead ph@(p, h)) as) = f $ \case
    FuncExpr (PureExprHead (_, "implies")) [FuncExpr (PureExprHead (_, "tuple")) ts, b]->
        checkArgs ts as >>= \x-> return (if x then ftype else Nothing)
    _-> writer (Nothing, [Message ph "Not function"]) 
    where
    checkArgs:: [Expr] -> [Expr] -> Writer [Message] Bool
    checkArgs [] [] = return True
    checkArgs [] _ = writer (False, [Message ph "Too few arguments"])
    checkArgs _ [] = writer (False, [Message ph "Too many arguments"])
    checkArgs (a:as) (t:ts) = checkType >>= \x-> let (a, msgs) = runWriter (checkArgs as ts) in writer (a||x, msgs) where
        checkType:: Writer [Message] Bool
        checkType = evalType tmap a >>= maybe (return False) (\x-> if equals t x 
            then return True 
            else writer (False, [Message (showCodeExpr a) ("The type is not '" ++ showExpr t ++ "'")]))
    ftype = M.lookup h tmap
    f:: (Expr -> Writer [Message] (Maybe Expr)) -> Writer [Message] (Maybe Expr)
    f g = maybe (writer (Nothing, [Message ph "Not defined"])) g ftype

isIdentOf:: String -> Expr -> Bool
isIdentOf t (IdentExpr (_, s)) = t == s
isIdentOf _ _ = False

isTypeType:: Expr -> Bool
isTypeType = isIdentOf "Type"

extractArgs:: String -> Expr -> [Expr]
extractArgs s e@(FuncExpr (PureExprHead (_, s')) as) = if s == s' then concatMap (extractArgs s) as else [e]
extractArgs s e = [e]

makeFuncType:: [Expr] -> Expr -> Expr
makeFuncType [arg] ret = FuncExpr (makeExprHead "->") [arg, ret]
makeFuncType args ret = FuncExpr (makeExprHead "->") [(FuncExpr $ makeExprHead "tuple") args, ret]

addIdent:: String -> Expr -> TypeMap -> Writer [Message] TypeMap
addIdent i t m = return $ M.insert i t m

conjMaybe:: [Maybe a] -> Maybe [a]
conjMaybe [] = Just []
conjMaybe (x:xs) = (:) <$> x <*> conjMaybe xs

makeTypeMap:: [Decla] -> TypeMap -> Writer [Message] TypeMap
makeTypeMap [] = addIdent "Prop" (makeIdentExpr "Type")
makeTypeMap (x:xs) = (>>= makeTypeMap xs) . (getType x) where
    getType:: Decla -> TypeMap -> Writer [Message] TypeMap
    getType (DataType (p, t) def) = \m-> do
        m' <- addIdent t (makeIdentExpr "Type") m
        addCstr cstrs m'
        where
        thisType = makeIdentExpr t
        cstrs = extractArgs "|" def
        addCstr:: [Expr] -> TypeMap -> Writer [Message] TypeMap
        addCstr [] m = return m
        addCstr (IdentExpr (_, i):xs) m = addIdent i thisType m >>= addCstr xs
        addCstr (FuncExpr (PureExprHead (_, i)) as:xs) m = do
            argsm <- mapM (evalType m) as
            let run x = maybe (return m) x (conjMaybe argsm)
            run $ \args-> do
                let cstrType = makeFuncType args thisType
                m' <- addIdent i cstrType m
                addCstr xs m'
        addCstr e m = error $ show e
    getType (Undef (_, t) e) = addIdent t e
    getType (Define (_, t) args ret def) = addIdent t (makeFuncType (toTypes args) ret) where
    getType _ = return
    toTypes:: VarDec -> [Expr]
    toTypes ((i, t):xs) = t:toTypes xs

makeScope:: TypeMap -> VarDec -> Writer [Message] TypeMap
makeScope gm xs = makeScope' gm xs M.empty where
    makeScope' gm ((ps@(p, s), e):xs) lm = evalType gm e 
        >>= maybe (return lm) (\x-> if isTypeType x 
                then return $ M.insert s x lm 
                else writer (lm, [Message ps ("Not type")]))
        >>= makeScope' gm xs

makeRules:: TypeMap -> [Expr] -> Writer [Message] ([Rule], [Rule])
makeRules tmap [] = return ([], [])
makeRules tmap (x:xs) = do
    result <- makeRule x
    (ms, mi) <- makeRules tmap xs
    return $ case result of 
        Nothing-> (ms, mi)
        Just (isStep, r)-> if isStep then (r:ms, mi) else (ms, r:mi) 
    where 
    -- expression -> (is step rule, rule)
    makeRule:: Expr -> Writer [Message] (Maybe (Bool, Rule))
    makeRule e@(FuncExpr (PureExprHead pk@(p, kind)) [a, b]) = case kind of
        ">>=" -> do
            at' <- evalType tmap a
            bt' <- evalType tmap b
            case (at', bt') of 
                (Just at, Just bt)-> if equals a b
                    then return $ Just (True, (a, b)) 
                    else writer (Nothing, [Message pk $ x ++ y]) where
                        x = "Left side type is'" ++ showExpr at ++ "', "
                        y = "but right side type is'" ++ showExpr bt ++ "'"
                _-> return Nothing
        "->" -> do
            et' <- evalType tmap e
            case et' of 
                Just et->
                    if isIdentOf "Prop" et 
                        then return $ Just (False, (a, b))
                        else writer (Nothing, [Message pk $ "Expected type is 'Prop', but actual type is" ++ showExpr et])
                Nothing-> return Nothing
        f -> writer (Nothing, [Message pk "Wrong function"])

toRuleMap:: [Rule] -> RuleMap
toRuleMap rs = toRuleMap' M.empty $ groupBy equalsHead rs where
    equalsHead (FuncExpr h _, _) (FuncExpr h' _, _) = showHead h == showHead h'
    getHead:: [Rule] -> String
    getHead ((FuncExpr h _, _):_) = showHead h
    toRuleMap':: RuleMap -> [[Rule]] -> RuleMap
    toRuleMap' = foldl (\m r-> M.insert (getHead r) r m)

makeRuleMap:: TypeMap -> [Expr] -> Writer [Message] (RuleMap, RuleMap, Simplicity)
makeRuleMap tmap xs = do
    (a, b) <- makeRules tmap xs
    simp <- makeSimp [] a
    let toAppSimp (a, b) = (appSimp simp a, appSimp simp b)
    let toMap = toRuleMap . map toAppSimp
    return (toMap a, toMap b, simp)

buildProgram:: String -> ((RuleMap, RuleMap, Simplicity), OpeMap, TypeMap, [Message])
buildProgram str = (rmap, omap, tmap, msgs ++ msgs') where
    (tmap, msgs') = runWriter $ makeTypeMap declas M.empty
    (rmap, msgs) = runWriter $ makeRuleMap tmap props
    ((declas, omap), rest) = runState parseProgram . tokenize $ str
    props = extractMaybe $ map toProp declas
    toProp:: Decla -> Maybe Expr
    toProp (Axiom _ p) = Just p
    toProp (Theorem _ p _) = Just p
    toProp _ = Nothing