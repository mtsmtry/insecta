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

simplifyM = onCtx ctxSRule simplify
derivateM = onCtx ctxIRule derivate

typeExpr:: Expr -> Analyzer (Maybe Expr)
typeExpr e@NumberExpr{} = return $ Just e
typeExpr e@StringExpr{} = return $ Just e
typeExpr (IdentExpr id@(StringIdent pos var)) = do
    ment <- lookupEnt var
    maybeFlip ment (analyzeErrorM id "Not defined") $ \ent->
        return $ Just $ IdentExpr (EntityIdent pos ent)
typeExpr (FuncExpr (StringIdent pos "->") [a, b]) = do
    marg <- typeExpr a
    mret <- typeExpr b
    case (marg, mret) of
        (Just arg, Just ret) -> return $ Just $ FuncExpr (FuncTypeIdent pos) [arg, ret]
        _ -> return Nothing
typeExpr (FuncExpr id@(StringIdent _ fun) as) = do
    ment <- lookupEnt fun
    margs <- mapM typeExpr as
    maybeFlip ment (analyzeErrorM id "Not defined") $ \ent->
        evalFunc (texpr ent) margs
    where
    evalFunc:: Expr -> [Maybe Expr] -> Analyzer (Maybe Expr)
    evalFunc (FuncExpr f@(FuncTypeIdent _) [targ, ret]) args = do
        let targs = extractExprsFromTuple targ
        if length targs /= length args
            then analyzeErrorM f "Argument number wrong"
            else do
                mapM_ (uncurry checkType) $ zip args targs
                return $ Just $ ret
    evalFunc e _ = do
        ps <- onOpeMap showCodeExpr e
        analyzeErrorM ps "Not function"
    checkType:: Maybe Expr -> Expr -> Analyzer ()
    checkType (Just value) texpr = unless (evalType value `equals` texpr) $ do
        vstr <- onOpeMap showExpr value
        tstr <- onOpeMap showExpr texpr
        let msg = "Couldn't match expected type '" ++ vstr ++ "' with actual type '" ++ tstr ++ "'"
        analyzeError (showIdent value) msg
    checkType _ _ = return ()

typeType = makeIdentExpr "Type"

newContext:: OpeMap -> Context
newContext omap = Context omap buildInScope [] M.empty M.empty M.empty M.empty M.empty where
    buildInTypes = ["Prop", "Char", "Type"]
    buildInScope = M.fromList $ map (, typeType) buildInTypes

returnMessage:: a -> Message -> Analyzer a
returnMessage a m = Analyzer $ \ctx-> ([m], ctx, a)

isIdentOf:: String -> Expr -> Bool
isIdentOf t (IdentExpr id) = t == show id
isIdentOf _ _ = False

isTypeType:: Expr -> Bool
isTypeType = isIdentOf "Type"

-- concat specified function arguments
-- ex. extractArgs "add" add(add(1, 2), add(3, 4)) => [1, 2, 3, 4]
extractArgs:: String -> Expr -> [Expr]
extractArgs str e@(FuncExpr f as) = if str == show f then concatMap (extractArgs str) as else [e]
extractArgs str e = [e]

-- ex. (1, 2) => [1, 2], x => [x]
extractExprsFromTuple:: Expr -> [Expr]
extractExprsFromTuple x@(FuncExpr f xs) = if show f == "tuple" then xs else [x]
extractExprsFromTuple x = [x]

-- (argument types, return type) -> function type
makeFuncType:: [Expr] -> Expr -> Expr
makeFuncType [arg] ret = FuncExpr (FuncTypeIdent NonePosition) [arg, ret]
makeFuncType args ret = FuncExpr (FuncTypeIdent NonePosition) [FuncExpr (StringIdent NonePosition "tuple") args, ret]

-- (identitfer, type, scope) -> new scope
addIdent:: Ident -> Expr -> Analyzer ()
addIdent id texpr = do
    if isTypeType (evalType texpr)
        then updateScope $ M.insert (show id) texpr
        else analyzeError id "Not type"

insertRule:: Expr -> Analyzer ()
insertRule rule = do
    nrule <- typeExpr rule
    case nrule of
        Just (FuncExpr f [a@(FuncExpr g _), b]) -> insertRule a b (show f) (show g)
        Just expr@FuncExpr{} -> analyzeError (showIdent expr) "Left side must be a function"
        Just expr -> analyzeError (showIdent expr) "wrong function"
        Nothing -> return ()
    where
    insertRule:: Expr -> Expr -> String -> String -> Analyzer ()
    insertRule before after ">>=" f = do
        addSimp before after
        updateSRule $ M.insertWith (++) f [(before, after)]
    insertRule before after "=>" f = updateIRule $ M.insertWith (++) f [(before, after)]
    insertRule before _ _ _ = analyzeError (showIdent before) "Wrong function"

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
        begin <- runCommand cmd input (FuncExpr (StringIdent NonePosition "=>") [ass, first])
        block <- runStatement first main
        return $ Rewrite EqualReason begin (FuncExpr (StringIdent NonePosition "=>") [ass, block])
    BlockStm stms -> runStms stms input where 
        runStms:: [Statement] -> Expr -> Analyzer Expr
        runStms xs input = foldM runStatement input xs

subScope::Analyzer a -> Analyzer a
subScope subRountine = do
    tmap <- fmap ctxTMap getContext
    res <- subRountine
    updateScope $ const tmap
    return res

loadVarDec:: (Ident, Expr) -> Analyzer ()
loadVarDec (ident, texpr) = do
    mnt <- typeExpr texpr
    maybeFlip mnt (return ()) $ \nt-> addIdent ident nt

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem decs prop stm) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    mnprop <- typeExpr prop
    maybeFlip mnprop (return ()) $ \nprop-> do
        case nprop of
            (FuncExpr _ [start, _]) -> runStatement start stm
        insertRule nprop

loadDecla (Axiom decs prop) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    insertRule prop

loadDecla (Undef id e mtex) = do
    addIdent id e
    case mtex of 
        Just tex -> updateLatex $ M.insert (show id) tex
        Nothing -> return ()

loadDecla (Define t args ret def) = do
    subScope $ do
        mapM_ (mapM_ loadVarDec) args
    addIdent t (makeFuncType (map snd (head args)) ret)

loadDecla (DataType id def) = do
    addIdent id typeType
    addCstr cstrs
    where
    thisType = makeIdentExpr (show id)
    cstrs = extractArgs "|" def
    addCstr:: [Expr] -> Analyzer ()
    addCstr [] = return ()
    addCstr (IdentExpr x:xs) = do
        addIdent x thisType
        addCstr xs
    addCstr (FuncExpr x as:xs) = do
        argsm <- mapM typeExpr as
        case conjMaybe argsm of
            Just args -> do
                let cstrType = makeFuncType (map evalType args) thisType
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