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
evalType tmap (IdentExpr (_, i)) = return $ M.lookup i tmap
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
        checkType = maybe False (equals t) <$> evalType tmap a
    ftype = M.lookup h tmap
    f:: (Expr -> Writer [Message] (Maybe Expr)) -> Writer [Message] (Maybe Expr)
    f g = maybe (writer (Nothing, [Message ph "Not defined"])) g ftype

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

buildProgram:: String -> ((RuleMap, RuleMap, Simplicity), OpeMap, TypeMap, [Message])
buildProgram str = (rmap, omap, tmap, msgs ++ msgs') where
    (rmap, msgs) = runWriter $ makeRuleMap props
    ((declas, omap), rest) = runState parseProgram . tokenize $ str
    (tmap, msgs') = runWriter $ makeTypeMap declas M.empty
    props = extractMaybe $ map toProp declas
    toProp:: Decla -> Maybe Expr
    toProp (Axiom _ p) = Just p
    toProp (Theorem _ p _) = Just p
    toProp _ = Nothing