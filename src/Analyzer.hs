module Analyzer where
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
import Parser
import Rewriter
import Data
import Visualizer

simplifyM:: Expr -> Analyzer Expr
simplifyM e = do
    ctx <- getContext
    let (simp, tmap, smap) = (ctxSimps ctx, ctxTMap ctx, ctxSRule ctx)
    return $ simplify simp tmap smap e

derivateM:: (Expr, Expr) -> Analyzer (Maybe Expr)
derivateM e = do
    ctx <- getContext
    let (imap, tmap) = (ctxSRule ctx, ctxTMap ctx)
    return $ derivate imap tmap e

typeType = makeIdentExpr "Type"
newContext omap = Context omap buildInScope [] M.empty M.empty M.empty where
    buildInTypes = ["Prop", "Char", "Type"]
    buildInScope = M.fromList $ map (, typeType) buildInTypes

returnMessage:: a -> Message -> Analyzer a
returnMessage a m = Analyzer $ \ctx-> ([m], ctx, a)

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

checkType:: Expr -> Expr -> Analyzer Bool
checkType t value = do
    atexpr <- evalType value
    omap <- fmap ctxOMap getContext
    case atexpr of
        Just at -> if equals t at
            then return True 
            else analyzeErrorB $ Message (showCodeExpr omap value) $
                "Couldn't match expected type '" ++ showExpr omap at ++
                "' with actual type '" ++ showExpr omap t ++ "'"
        Nothing -> return False

evalType:: Expr -> Analyzer (Maybe Expr)
evalType NumberExpr{} = return $ Just $ makeIdentExpr "N"
evalType StringExpr{} = return $ Just $ makeIdentExpr "Char"
evalType (IdentExpr ph@(_, h)) = do
    texpr <- fmap (M.lookup h . ctxTMap) getContext
    case texpr of
        Just t -> return $ Just t
        Nothing -> analyzeErrorM $ Message ph "Not defined"
evalType (FuncExpr (_, "->") [arg, ret]) = do
    forM_ (extractExprsFromTuple arg) $ checkType typeType
    checkType typeType ret
    return $ Just typeType
evalType (FuncExpr ph@(p, h) as) = do
    texpr <- fmap (M.lookup h . ctxTMap) getContext
    case texpr of
        Just t -> evalFuncRetType t
        Nothing -> analyzeErrorM $ Message ph "Not defined"
    where
    -- function type -> function return type
    evalFuncRetType:: Expr -> Analyzer (Maybe Expr)
    evalFuncRetType = \case
        FuncExpr (_, "->") [arg, ret] -> do
            successful <- checkArgs (extractExprsFromTuple arg) as
            return (if successful then Just ret else Nothing)
        _ -> analyzeErrorM $ Message ph "Not function"
    -- (argument values, argument types) -> is successful
    checkArgs:: [Expr] -> [Expr] -> Analyzer Bool
    checkArgs [] [] = return True
    checkArgs _ [] = analyzeErrorB $ Message ph "Too few arguments"
    checkArgs (t:ts) (a:as) = do
        res <- checkType t a
        rest <- checkArgs ts as
        return $ res || rest

-- (argument types, return type) -> function type
makeFuncType:: [Expr] -> Expr -> Expr
makeFuncType [arg] ret = FuncExpr (NonePosition, "->") [arg, ret]
makeFuncType args ret = FuncExpr (NonePosition, "->") [FuncExpr (NonePosition, "tuple") args, ret]

-- (identitfer, type, scope) -> new scope
addIdent:: PosStr -> Expr -> Analyzer ()
addIdent ps@(_, s) t = do
    texpr <- evalType t
    case texpr of 
        Nothing -> return ()
        Just typeOfType -> if isTypeType typeOfType
            then updateScope $ M.insert s t
            else analyzeError $ Message ps "Not type"

getName (FuncExpr (_, f) _) = f
-- (scope, expression) -> (is step rule, rule)
insertRule:: Expr -> Analyzer ()
insertRule e@(FuncExpr pk@(p, kind) [a@(FuncExpr (_, h) _), b]) = insertRule' kind where
    insertRule':: String -> Analyzer ()
    insertRule' ">>=" = do
        at' <- evalType a
        bt' <- evalType b
        case (at', bt') of
            (Just at, Just bt)-> if equals at bt
                then do
                    addSimp a b
                    updateSRule $ M.insertWith (++) (getName a) [(a, b)]
                else do
                    left <- onOpeMap showExpr at
                    right <- onOpeMap showExpr bt
                    let msg = "Left side type is '" ++ left ++ "', " ++ "but right side type is '" ++ right ++ "'"
                    analyzeError $ Message pk msg
            _-> return ()
    insertRule' "=>" = do 
        et' <- evalType e
        case et' of
            Just et-> if isIdentOf "Prop" et 
                then updateIRule $ M.insertWith (++) (getName a) [(a, b)]
                else do
                    str <- onOpeMap showExpr et
                    analyzeError $ Message pk $ "Couldn't match expected type 'Prop' with actual type '" ++ str ++ "'"
            Nothing-> return ()
    insertRule' f = analyzeError $ Message pk "Wrong function"

insertRule e@(FuncExpr _ _) = do 
    ps <- onOpeMap showCodeExpr e
    analyzeError $ Message ps "This is not a function"

insertRule e = do
    ps <- onOpeMap showCodeExpr e
    analyzeError $ Message ps "This is not a function"

runCommand:: Command -> Expr -> Expr -> Analyzer Expr
runCommand StepCmd goal input = do
    strg <- simplifyM input
    sgoal <- simplifyM goal
    case mergeRewrite strg sgoal of
        Just proof -> return strg
        Nothing -> do
            st <- onOpeMap showLatestExpr strg
            sg <- onOpeMap showLatestExpr sgoal
            ps <- onOpeMap showCodeExpr goal
            let msg = "Couldn't match simplified terms with '" ++ st ++ "' and '" ++ sg ++ "'"
            returnMessage sgoal $ Message ps msg
runCommand ImplCmd goal input = do
    res <- derivateM (input, goal)
    case res of
        Just proof -> return proof
        Nothing -> do 
            ps <- onOpeMap showCodeExpr goal
            b <- onOpeMap showLatestExpr input
            returnMessage goal $ Message ps $ "Couldn't derivate from '" ++ b ++ "'"

runStatement:: Expr -> Statement -> Analyzer Expr
runStatement input = \case
    SingleStm cmd goal -> runCommand cmd goal input
    AssumeStm cmd ass first main -> do
        -- P => X -> [A, B, C]
        -- [P, Q, X -> [A, B, C]]
        begin <- runCommand cmd input (FuncExpr (NonePosition, "->") [ass, first])
        block <- runStatement first main
        return $ Rewrite EqualReason begin (FuncExpr (NonePosition, "->") [ass, block])
    BlockStm stms -> runStms stms input where 
        runStms:: [Statement] -> Expr -> Analyzer Expr
        runStms xs input = foldM runStatement input xs

subScope::Analyzer a -> Analyzer a
subScope subRountine = do
    tmap <- fmap ctxTMap getContext
    res <- subRountine
    updateScope $ const tmap
    return res

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem dec prop stm) = subScope $ do
    mapM_ (uncurry addIdent) dec
    case prop of
        FuncExpr ps@(p, kind) [start, goal] -> case kind of 
            "=>" -> do
                res <- runStatement start stm
                return ()
        _ -> do
            str <- onOpeMap showCodeExpr prop
            analyzeError $ Message str "Neither '>>=' or '=>'"
    insertRule prop

loadDecla (Axiom dec prop) = subScope $ do
    mapM_ (uncurry addIdent) dec
    insertRule prop

loadDecla (Undef t@(_, s) e mtex) = do
    addIdent t e
    case mtex of 
        Just tex -> updateLatex $ M.insert s tex
        Nothing -> return ()

loadDecla (Define t args ret def) = do
    subScope $ do
        mapM_ (uncurry addIdent) args
    addIdent t (makeFuncType (map snd args) ret)

loadDecla (DataType t@(_, i) def) = do
    addIdent t typeType
    addCstr cstrs
    where
    thisType = makeIdentExpr i
    cstrs = extractArgs "|" def
    addCstr:: [Expr] -> Analyzer ()
    addCstr [] = return ()
    addCstr (IdentExpr x:xs) = do
        addIdent x thisType
        addCstr xs
    addCstr (FuncExpr x as:xs) = do
        argsm <- mapM evalType as
        case conjMaybe argsm of
            Just args -> do
                let cstrType = makeFuncType args thisType
                addIdent x cstrType
                addCstr xs
            Nothing -> return ()
    addCstr e = error $ show e

loadDecla _ = return ()

buildProgram::String -> ([Message], Context)
buildProgram prg = (msg ++ msg' ++ msg'', ctx) where
    (msg, pos, rest, tokens) = runLexer tokenize (initialPosition, prg)
    (msg', rest', (declas, omap)) = runParser parseProgram tokens
    (msg'', ctx, _) = analyze (mapM_ loadDecla declas) (newContext omap)