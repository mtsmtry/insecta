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

data Context = Context TypeMap Simplicity (RuleMap, RuleMap)

typeType = makeIdentExpr "Type"
newContext = Context buildInScope [] (M.empty, M.empty) where
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
extractArgs s e@(FuncExpr (_, s') as) = if s == s' then concatMap (extractArgs s) as else [e]
extractArgs s e = [e]

-- ex. (1, 2) => [1, 2], x => [x]
extractExprsFromTuple:: Expr -> [Expr]
extractExprsFromTuple (FuncExpr (_, "tuple") xs) = xs
extractExprsFromTuple x = [x]

-- (scope, expression) -> type
evalType:: TypeMap -> Expr -> Writer [Message] (Maybe Expr)
evalType tmap NumberExpr{} = return $ Just $ makeIdentExpr "N"
evalType tmap StringExpr{} = return $ Just $ makeIdentExpr "Char"
evalType tmap (IdentExpr ph@(_, h)) = maybe (writer (Nothing, [Message ph "Not defined"])) (return . Just) (M.lookup h tmap)
evalType tmap (FuncExpr ph@(p, h) as) = maybe (writer (Nothing, [Message ph "Not defined"])) evalFuncRetType (M.lookup h tmap) 
    where
    -- function type -> function return type
    evalFuncRetType:: Expr -> Writer [Message] (Maybe Expr)
    evalFuncRetType = \case
        FuncExpr (_, "->") [arg, ret] -> do
            successful <- checkArgs as (extractExprsFromTuple arg)
            return (if successful then Just ret else Nothing)
        _ -> writer (Nothing, [Message ph "Not function"])
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

-- (argument types, return type) -> function type
makeFuncType:: [Expr] -> Expr -> Expr
makeFuncType [arg] ret = FuncExpr (NonePosition, "->") [arg, ret]
makeFuncType args ret = FuncExpr (NonePosition, "->") [FuncExpr (NonePosition, "tuple") args, ret]

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
                else writer (lm, [Message ps "Not type"]))
        >>= makeScope' gm xs

-- (scope, expression) -> (is step rule, rule)
makeRule:: Simplicity -> TypeMap -> Expr -> Writer [Message] (Maybe (Bool, String, Rule, Simplicity))
makeRule smap tmap e@(FuncExpr pk@(p, kind) [a@(FuncExpr (_, h) _), b]) = case kind of
    ">>=" -> do
        at' <- evalType tmap a
        bt' <- evalType tmap b
        case (at', bt') of
            (Just at, Just bt)-> if equals at bt
                then do 
                    smap' <- addSimp smap a b
                    return $ Just (True, h, (a, b), smap') 
                else writer (Nothing, [Message pk $ x ++ y]) where
                    x = "Left side type is '" ++ showExpr at ++ "', "
                    y = "but right side type is '" ++ showExpr bt ++ "'"
            _-> return Nothing
    "->" -> do
        et' <- evalType tmap e
        case et' of
            Just et-> if isIdentOf "Prop" et 
                then return $ Just (False, h, (a, b), smap)
                else writer (Nothing, [Message pk $ "Couldn't match expected type 'Prop' with actual type '" ++ showExpr et ++ "'"])
            Nothing-> return Nothing
    f -> writer (Nothing, [Message pk "Wrong function"])
makeRule _ _ e@(FuncExpr _ _) = writer (Nothing, [Message (showCodeExpr e) "This is not a function"])
makeRule _ _ e = writer (Nothing, [Message (showCodeExpr e) "This is not a function"])

insertRule:: Simplicity -> TypeMap -> Expr -> (RuleMap, RuleMap) -> Writer [Message] ((RuleMap, RuleMap), Simplicity)
insertRule simp tmap prop rset@(smap, imap) = do
    mrule <- makeRule simp tmap prop
    return $ case mrule of
        Just (True, name, rule, simp') -> ((M.insertWith (++) name [rule] smap, imap), simp')
        Just (False, name, rule, simp') -> ((smap, M.insertWith (++) name [rule] imap), simp')
        Nothing -> (rset, simp)

runCommand:: Simplicity -> TypeMap -> (RuleMap, RuleMap) -> Command -> Expr -> Expr -> Writer [Message] Expr
runCommand simp tmap (smap, _) StepCmd goal input = case mergeRewrite strg sgoal of
    Just proof -> return strg
    Nothing -> writer (sgoal, [Message (showCodeExpr goal) $ "Couldn't match simplified terms with '" ++ 
        showLatestExpr strg ++ "' and '" ++ showLatestExpr sgoal ++ "'"])
    where 
        (strg, sgoal) = (simplify simp tmap smap input, simplify simp tmap smap goal)
runCommand s tmap (_, imap) ImplCmd goal input = case derivate imap tmap (input, goal) of
    Just proof -> return proof
    Nothing -> (writer (goal, [Message (showCodeExpr goal) $ "Couldn't derivate from '" ++ showLatestExpr input ++ "'"]))

runStatement:: Simplicity -> TypeMap -> (RuleMap, RuleMap) -> Expr -> Statement -> Writer [Message] Expr
runStatement simp tmap rmap input = \case
    SingleStm cmd goal -> runCommand simp tmap rmap cmd goal input
    AssumeStm cmd ass first main -> do
        -- P => X -> [A, B, C]
        -- [P, Q, X -> [A, B, C]]
        begin <- runCommand simp tmap rmap cmd input (FuncExpr (NonePosition, "->") [ass, first])
        block <- runStatement simp tmap rmap first main
        return $ Rewrite EqualReason begin (FuncExpr (NonePosition, "->") [ass, block])
    BlockStm stms -> runStms stms input where 
        runStms:: [Statement] -> Expr -> Writer [Message] Expr
        runStms (x:xs) input = do
            ntrg <- runStatement simp tmap rmap input x
            runStms xs ntrg

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Context -> Writer [Message] Context
loadDecla (Theorem dec prop stm) (Context tmap simp rset) = do
    lm <- makeScope tmap dec
    let scope = M.union lm tmap
    res <- runStatement simp tmap rset prop stm
    (rset', simp') <- insertRule simp scope prop rset
    return $ Context tmap simp' rset'

loadDecla (Axiom dec prop) (Context tmap simp rset) = do
    lm <- makeScope tmap dec
    let scope = M.union lm tmap
    (rset', simp')  <- insertRule simp scope prop rset
    return $ Context tmap simp' rset'

loadDecla (Undef (_, t) e) (Context tmap simp rset) = do
    tmap' <- addIdent t e tmap
    return $ Context tmap' simp rset

loadDecla (Define (_, t) args ret def) (Context tmap simp rset) = do
    lm <- makeScope tmap args
    let scope = M.union lm tmap
    tmap' <- addIdent t (makeFuncType (map snd args) ret) tmap
    return $ Context tmap' simp rset

loadDecla (DataType (p, t) def) (Context tmap simp rset) = do
    tmap' <- addIdent t (makeIdentExpr "Type") tmap
    addCstr cstrs tmap'
    return $ Context tmap' simp rset
    where
    thisType = makeIdentExpr t
    cstrs = extractArgs "|" def
    -- (constructers, scope) -> new scope
    addCstr:: [Expr] -> TypeMap -> Writer [Message] TypeMap
    addCstr [] m = return m
    addCstr (IdentExpr (_, i):xs) m = addIdent i thisType m >>= addCstr xs
    addCstr (FuncExpr (_, i) as:xs) m = do
        argsm <- mapM (evalType m) as
        let run x = maybe (return m) x (conjMaybe argsm)
        run $ \args-> do
            let cstrType = makeFuncType args thisType
            m' <- addIdent i cstrType m
            addCstr xs m'
    addCstr e m = error $ show e

loadDecla _ ctx = return ctx

buildProgram::String -> Writer [Message] (OpeMap, Context)
buildProgram prg = do 
    ctx <- loadDeclas declas newContext
    return (omap, ctx)
    where
    tokens = tokenize prg
    ((declas, omap), rest) = runState parseProgram tokens
    loadDeclas [] ctx = return ctx
    loadDeclas (x:xs) ctx = do
        ctx' <- loadDecla x ctx
        loadDeclas xs ctx'