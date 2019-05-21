module Analyzer where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Library
import Parser
import Rewriter

type TypeMap = M.Map String Expr

typeType = makeIdentExpr "Type"
buildInTypes = ["Prop", "Char"]
buildInScope = M.fromList $ map (\x-> (x, typeType)) buildInTypes

isIdentOf:: String -> Expr -> Bool
isIdentOf t (IdentExpr (_, s)) = t == s
isIdentOf _ _ = False

isTypeType:: Expr -> Bool
isTypeType = isIdentOf "Type"

-- concat specified function arguments
-- ex. extractArgs "add" add(add(1, 2), add(3, 4)) => [1, 2, 3, 4]
extractArgs:: String -> Expr -> [Expr]
extractArgs s e@(FuncExpr (PureExprHead (_, s')) as) = if s == s' then concatMap (extractArgs s) as else [e]
extractArgs s e = [e]

-- ex. (1, 2) => [1, 2], x => [x]
extractExprsFromTuple:: Expr -> [Expr]
extractExprsFromTuple (FuncExpr (PureExprHead (_, "tuple")) xs) = xs
extractExprsFromTuple x = [x]

-- (argument values, argument types) -> is successful
checkArgs:: [Expr] -> [Expr] -> Writer [Message] Bool
checkArgs [] [] = return True
checkArgs [] _ = writer (False, [Message ph "Too few arguments"])
checkArgs _ [] = writer (False, [Message ph "Too many arguments"])
checkArgs (a:as) (t:ts) = checkType >>= \x-> let (a, msgs) = runWriter (checkArgs as ts) in writer (a||x, msgs) where
    checkType:: Writer [Message] Bool
    checkType = evalType tmap a >>= maybe (return False) (\x-> if equals t x 
        then return True 
        else writer (False, [Message (showCodeExpr a) ("Couldn't match expected type '" ++ showExpr x ++ "' with actual type '" ++ showExpr t ++ "'")]))

-- (scope, expression) -> type
evalType:: TypeMap -> Expr -> Writer [Message] (Maybe Expr)
evalType tmap NumberExpr{} = return $ Just $ makeIdentExpr "N"
evalType tmap StringExpr{} = return $ Just $ makeIdentExpr "Char"
evalType tmap (IdentExpr ph@(_, h)) = passType $ return . Just
evalType tmap (FuncExpr (PureExprHead ph@(p, h)) as) = passType evalFuncRetType where
    passType f = maybe (writer (Nothing, [Message ph "Not defined"])) f (M.lookup h tmap)
    -- function type -> function return type
    evalFuncRetType:: Expr -> Writer [Message] (Maybe Expr)
    evalFuncRetType = \case
        FuncExpr (PureExprHead (_, "->")) [arg, ret] -> do
            successful <- checkArgs as (extractExprsFromTuple arg)
            return (if successful then Just ret else Nothing)
        _ -> writer (Nothing, [Message ph "Not function"])

-- (argument types, return type) -> function type
makeFuncType:: [Expr] -> Expr -> Expr
makeFuncType [arg] ret = FuncExpr (makeExprHead "->") [arg, ret]
makeFuncType args ret = FuncExpr (makeExprHead "->") [(FuncExpr $ makeExprHead "tuple") args, ret]

-- (identitfer, type, scope) -> new scope
addIdent:: String -> Expr -> TypeMap -> Writer [Message] TypeMap
addIdent i t m = return $ M.insert i t m

-- (outer scope, variable declarations) -> output scope
makeScope:: TypeMap -> VarDec -> Writer [Message] TypeMap
makeScope gm xs = makeScope' gm xs M.empty where
    makeScope' gm [] lm = return lm
    makeScope' gm ((ps@(p, s), e):xs) lm = evalType gm e
        >>= maybe (return lm) (\x-> if isTypeType x 
                then return $ M.insert s e lm 
                else writer (lm, [Message ps ("Not type")]))
        >>= makeScope' gm xs

-- (scope, expression) -> (is step rule, rule)
makeRule:: TypeMap -> Expr -> Writer [Message] (Maybe (Bool, String, Rule))
makeRule tmap e@(FuncExpr (PureExprHead pk@(p, kind)) [a@(FuncExpr h _), b]) = case kind of
    ">>=" -> do
        at' <- evalType tmap a
        bt' <- evalType tmap b
        case (at', bt') of
            (Just at, Just bt)-> if equals at bt
                then return $ Just (True, showHead h, (a, b)) 
                else writer (Nothing, [Message pk $ x ++ y]) where
                    x = "Left side type is '" ++ showExpr at ++ "', "
                    y = "but right side type is '" ++ showExpr bt ++ "'"
            _-> return Nothing
    "->" -> do
        et' <- evalType tmap e
        case et' of
            Just et-> if isIdentOf "Prop" et 
                then return $ Just (False, showHead h, (a, b))
                else writer (Nothing, [Message pk $ "Couldn't match expected type 'Prop' with actual type '" ++ showExpr et ++ "'"])
            Nothing-> return Nothing
    f -> writer (Nothing, [Message pk "Wrong function"])
makeRule _ e@(FuncExpr (PureExprHead _) _) = writer (Nothing, [Message (showCodeExpr e) "This is not a function"])
makeRule _ e = writer (Nothing, [Message (showCodeExpr e) "This is not a function"])

insertRule:: TypeMap -> Expr -> (RuleMap, RuleMap) -> Writer [Message] (RuleMap, RuleMap)
insertRule tmap prop rset@(smap, imap) = do
    mrule <- makeRule tmap prop
    return $ case mrule of
        Just (True, name, rule) -> (M.adjust (rule:) name smap, imap)
        Just (False, name, rule) -> (smap, M.adjust (rule:) name imap)
        Nothing -> rset

runStatement:: (RuleMap, RuleMap) -> Statement -> Expr -> Writer [Message] Expr
runStatement (smap, imap) stm@(SingleStm cmd goal) input = case cmd of
    StepCmd -> case margeRewrite strg sgoal of
        Just proof -> return strg
        Nothing -> writer (sgoal, [Message (showCodeExpr goal) $ "Couldn't match simplified terms with '" ++ 
            showExprLatest strg ++ "' and '" ++ showExprLatest sgoal ++ "'"])
        where 
            (strg, sgoal) = (simplify smap input, simplify smap goal)
    ImplCmd -> case derivate imap (input, goal) of
        Just proof -> return proof
        Nothing -> (writer (goal, [Message (showCodeExpr goal) $ "Couldn't derivate from '" ++ showExprLatest input ++ "'"]))
runStatement rset stm@(AssumeStm cmd ass first main) trg = 
    return ass
runStatement rset stm@(BlockStm stms) trg = runStms stms trg <$> BlockStm where 
    runStms:: [Statement] -> Expr -> Writer [Message] [Statement]
    runStms (x:xs) trg = do
        (stm, ntrg) <- runStatement rset x trg
        rest <- runStms xs ntrg
        return $ stm:rest

data Context = Context TypeMap Simplicity (RuleMap, RuleMap)

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Context -> Writer [Message] Context
loadDecla (Theorem dec prop stm) (Context tmap simp rset) = do
    lm <- makeScope tmap dec
    let scope = M.union lm gm
    res <- runStatement rset stm prop
    rset' <- insertRule tmap prop rset
    return (tmap, rset')
    -- tmap' <- addDeclaToGlobal dec tmap

loadDecla (Axiom dec prop) (Context tmap simp rset) = do
    rset' <- insertRule tmap prop rset
    return (tmap, rset')

loadDecla (Undef (_, t) e) (Context tmap simp rset) = do
    tmap' <- addIdent t e tmap
    return Context tmap' simp rset

loadDecla (Define (_, t) args ret def) (Context tmap simp rset) = do
    tmap' <- addIdent t (makeFuncType (toTypes args) ret)
    return Context tmap' simp rset

loadDecla (DataType (p, t) def) (Context tmap simp rset) = do
    tmap' <- addIdent t (makeIdentExpr "Type") tmap
    addCstr cstrs tmap'
    return Context tmap' simp rset
    where
    thisType = makeIdentExpr t
    cstrs = extractArgs "|" def
    -- (constructers, scope) -> new scope
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