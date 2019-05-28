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
-- import Visualizer

isAssociative:: Rule -> Bool
isAssociative (FunExpr f [IdentExpr a, IdentExpr b], FunExpr g [IdentExpr p, IdentExpr q]) = 
    f == g && a == q && b == p
isAssociative _ = False

isCommutative:: Rule -> Bool
isCommutative (FunExpr f [FunExpr g [IdentExpr a, IdentExpr b], IdentExpr c], 
               FunExpr h [IdentExpr x, FunExpr i [IdentExpr y, IdentExpr z]]) = 
    all (==f) [g, h, i] && all (uncurry (==)) [(a, x), (b, y), (c, z)]
isCommutative _ = False

simplifyM = onCtx ctxSRule simplify
derivateM = onCtx ctxIRule derivate

buildFormula:: Expr -> Analyzer (Maybe Formula)
buildFormula (NumberExpr num) = return $ Just $ Formula (NumFormula num) (makeTypeFormula "N")
buildFormula (StringExpr str) = return $ Just $ Formula (StrFormula str) (makeTypeFormula "String")

buildFormula (IdentExpr id@(Ident pos var)) = do
    ment <- lookupEnt var
    maybeFlip ment (analyzeErrorM id "Not defined") $ \ent->
        return $ Just $ VarFormula (EntityIdent pos ent)

buildFormula (FunExpr id@(Ident pos ">>=") [a, b]) = do
    ma <- buildFormula a
    mb <- buildFormula b
    case (ma, mb) of
        (Just na, Just nb) -> if evalType na == evalType nb 
            then return $ Just $ FunFormula (Ident pos ">>=") [na, nb]
            else analyzeErrorM id "Not match type"
        _ -> return Nothing

buildFormula (FunExpr (Ident pos "->") [a, b]) = do
    margs <- conjMaybe <$> mapM buildFormula (extractFormulasFromTuple a)
    mret <- buildFormula b
    case (margs, mret) of
        (Just args, Just ret) -> return $ Just $ FunFormula (FuncTypeIdent pos) [FunFormula (StringIdent NonePosition "tuple") args, ret]
        _ -> return Nothing

buildFormula e@(FunExpr id@(Ident pos fun) args) = do
    ment <- lookupEnt fun
    margs <- mapM buildFormula args
    maybeFlip ment (analyzeErrorM id "Not defined") $ \ent-> do
        checkFunc (tFormula ent) margs
        case conjMaybe margs of
            Just nargs -> return $ Just $ FunFormula (EntityIdent pos ent) nargs
            Nothing -> return Nothing
    where
    checkFunc:: Formula -> [Maybe Formula] -> Analyzer Bool
    checkFunc (FunFormula f@(Ident _ _) [defArg, ret]) inputArgs = do
        let typeArgs = extractFormulasFromTuple defArg
        if length typeArgs /= length inputArgs
            then analyzeErrorB f "Argument number wrong"
            else do
                mapM_ (uncurry checkType) $ zip inputArgs typeArgs
                return False
    checkFunc e _ = do
        ps <- onOpeMap showCodeFormula e
        analyzeErrorB ps $ "Not function:" ++ show ps
    checkType:: Maybe Formula -> Formula -> Analyzer ()
    checkType (Just value) def = let input = evalType value in unless (input == def) $ do
        vstr <- onOpeMap showFormula input
        tstr <- onOpeMap showFormula def
        let msg = "Couldn't match expected type '" ++ vstr ++ "' with actual type '" ++ tstr ++ "'"
        analyzeError (showIdent value) msg
    checkType _ _ = return ()
    
buildFormula e = return Nothing -- error $ "Wrong pattern:" ++ show e 

-- ex. (1, 2) => [1, 2], x => [x]
extractFormulasFromTuple:: Formula -> [Formula]
extractFormulasFromTuple x@(FunFormula f xs) = if show f == "tuple" then xs else [x]
extractFormulasFromTuple x = [x]

returnMessage:: a -> Message -> Analyzer a
returnMessage a m = Analyzer $ \ctx-> ([m], ctx, a)

isIdentOf:: String -> Formula -> Bool
isIdentOf t (VarFormula id) = t == show id
isIdentOf _ _ = False

isTypeType:: Formula -> Bool
isTypeType = isIdentOf "Type"

-- concat specified function arguments
-- ex. extractArgs "add" add(add(1, 2), add(3, 4)) => [1, 2, 3, 4]
extractArgs:: String -> Formula -> [Formula]
extractArgs str e@(FunFormula f as) = if str == show f then concatMap (extractArgs str) as else [e]
extractArgs str e = [e]

-- (argument types, return type) -> function type
makeFuncType:: [Formula] -> Formula -> Formula
makeFuncType [arg] ret = FunFormula (FuncTypeIdent NonePosition) [arg, ret]
makeFuncType args ret = FunFormula (FuncTypeIdent NonePosition) [FunFormula (StringIdent NonePosition "tuple") args, ret]

insertRule:: Formula -> Analyzer ()
insertRule rule = do
    nrule <- buildFormula rule
    case nrule of
        Just (FunFormula f [a@(FunFormula g _), b]) -> insertRule a b (show f) (show g)
        Just fom@FunFormula{} -> analyzeError (showIdent fom) "Left side must be a function"
        Just fom -> analyzeError (showIdent fom) "wrong function"
        Nothing -> return ()
    where
    insertRule:: Formula -> Formula -> String -> String -> Analyzer ()
    insertRule before after ">>=" f = do
        insertSimp before after
        updateSRule $ M.insertWith (++) f [(before, after)]
    insertRule before after "=>" f = updateIRule $ M.insertWith (++) f [(before, after)]
    insertRule before _ _ _ = analyzeError (showIdent before) "Wrong function"

runCommand:: Command -> Formula -> Formula -> Analyzer Formula
runCommand StepCmd goal input = do
    strg <- simplifyM input
    sgoal <- simplifyM goal
    case mergeRewrite strg sgoal of
        Just proof -> return strg
        Nothing -> do
            st <- onOpeMap showLatestFormula strg
            sg <- onOpeMap showLatestFormula sgoal
            ps <- onOpeMap showCodeFormula goal
            let msg = "Couldn't match simplified terms with '" ++ st ++ "' and '" ++ sg ++ "'"
            returnMessage sgoal $ Message ps msg
runCommand ImplCmd goal input = do
    res <- derivateM (input, goal)
    case res of
        Just proof -> return proof
        Nothing -> do 
            ps <- onOpeMap showCodeFormula goal
            b <- onOpeMap showLatestFormula input
            returnMessage goal $ Message ps $ "Couldn't derivate from '" ++ b ++ "'"

runStatement:: Formula -> Statement -> Analyzer Formula
runStatement input = \case
    SingleStm cmd goal -> runCommand cmd goal input
    AssumeStm cmd ass first main -> do
        -- P => X -> [A, B, C]
        -- [P, Q, X -> [A, B, C]]
        begin <- runCommand cmd input (FunFormula (StringIdent NonePosition "=>") [ass, first])
        block <- runStatement first main
        return $ Rewrite EqualReason begin (FunFormula (StringIdent NonePosition "=>") [ass, block])
    BlockStm stms -> runStms stms input where 
        runStms:: [Statement] -> Formula -> Analyzer Formula
        runStms xs input = foldM runStatement input xs

subScope::Analyzer a -> Analyzer a
subScope subRountine = do
    tmap <- fmap ctxScope getContext
    res <- subRountine
    updateScope $ const tmap
    return res

loadVarDec:: (Ident, Formula) -> Analyzer ()
loadVarDec (id, tFormula) = do
    mnt <- buildFormula tFormula
    maybe (return ()) (addIdent False id) mnt

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem decs prop stm) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    mnprop <- buildFormula prop
    maybeFlip mnprop (return ()) $ \nprop-> do
        case nprop of
            (FunFormula _ [start, _]) -> return () -- Just <$> runStatement start stm
            _ -> analyzeError (showIdent prop) "Not function"
        insertRule nprop

loadDecla (Axiom decs prop) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    insertRule prop

loadDecla (Undef id tFormula mtex) = do
    mnt <- buildFormula tFormula
    maybe (return ()) (addIdent True id) mnt
    case mtex of 
        Just tex -> updateLatex $ M.insert (show id) tex
        Nothing -> return ()

loadDecla (Define t args ret def) = do
    subScope $ do
        mapM_ (mapM_ loadVarDec) args
    addIdent True t (makeFuncType (map snd (head args)) ret)

loadDecla (DataType id def) = do
    addIdent True id typeType
    addCstr cstrs
    where
    thisType = makeVarFormula (show id)
    cstrs = extractArgs "|" def
    addCstr:: [Formula] -> Analyzer ()
    addCstr [] = return ()
    addCstr (VarFormula x:xs) = do
        addIdent True x thisType
        addCstr xs
    addCstr (FunFormula x as:xs) = do
        argsm <- mapM buildFormula as
        case conjMaybe argsm of
            Just args -> do
                let cstrType = makeFuncType (map evalType args) thisType
                addIdent True x cstrType
                addCstr xs
            Nothing -> return ()
    addCstr e = error $ show e

loadDecla _ = return ()

buildProgram::String -> ([Message], Context)
buildProgram prg = (msg ++ msg', ctx) where
    (msg, declas, omap) = parseProgram prg
    (msg', ctx, _) = analyze (mapM_ loadDecla declas) (newContext omap)