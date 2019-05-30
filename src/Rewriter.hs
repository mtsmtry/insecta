module Rewriter(unify, assign, simplify, derivate, derivateUnfold, derivateExists, insertSimp, mergeRewrite) where
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
import Data

(<||>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
a <||> b = \m-> a m <|> b m
(<&&>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
a <&&> b = \m-> a m >>= \m'-> b m'

unify:: Fom -> Fom -> Maybe AssignMap
unify ptn trg = unifym ptn trg M.empty

unifyFun:: ([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyFun unifyArgs ptn trg = if funName ptn /= funName trg then const Nothing else \m-> do
    tyAsg <- unifym (funType ptn) (funType trg) m
    vlAsg <- unifyArgs (funArgs ptn) (funArgs trg) tyAsg
    return $ M.union tyAsg vlAsg

unifym:: Fom -> Fom -> AssignMap -> Maybe AssignMap
unifym Rewrite{} _ = const $ error "Do not use Rewrite in a rule"
unifym ptn trg@Rewrite{} = unifym ptn $ rewLater trg
unifym TypeOfType TypeOfType = id . Just
unifym ptn@(CstFom id ty) trg@(CstFom id' ty') = if id == id' then unifym ty ty' else const Nothing
unifym ptn@NumFom{} trg = if ptn == trg then id . Just else const Nothing
unifym ptn@StrFom{} trg = if ptn == trg then id . Just else const Nothing

unifym ptn@(VarFom id ty) trg = \m-> case M.lookup (idStr id) m of
    Just x -> if x == trg then Just m else Nothing
    Nothing -> Just $ M.insert (idStr id) (latestFom trg) m

unifym ptn@(FunFom OFun _ _ _) trg@(FunFom OFun _ _ _) = unifyFun unifyArgs ptn trg where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs (e:ex) (e':ex') = unifym e e' <&&> unifyArgs ex ex'
    unifyArgs [] [] = id . Just
    unifyArgs _ _ = const Nothing

unifym ptn@(FunFom CFun _ _ _) trg@(FunFom CFun _ _ _) = unifyFun unifyArgs ptn trg where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [a, b] [a', b'] = (unifym a a' <&&> unifym b b') <||> (unifym a b' <&&> unifym b a')

unifym ptn@(FunFom (ACFun rest) _ _ _) trg@(FunFom (ACFun rest') f ty _) = unifyFun unifyArgs ptn trg where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [] trgs = Just . M.insert rest (FunFom (ACFun "") f ty trgs)
    unifyArgs (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs where
    matchForPtn:: Fom -> [Fom] -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    matchForPtn ptn ptns noMatchTrgs [] = const Nothing
    matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
        main = unifym ptn trg <&&> unifyArgs ptns (noMatchTrgs ++ restTrgs)
        rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs

unifym _ _ = const Nothing

assign:: AssignMap -> Fom -> Fom
assign m fom@(VarFom id ty) = fromMaybe fom $ M.lookup (idStr id) m
assign m fom = applyArgs (assign m) fom

insertSimp:: Ident -> Fom -> Fom -> Analyzer ()
insertSimp id a b = case (funIdent a, funIdent b) of
    (Just fn, Just gn) -> insertSimpByName (idStr fn) (idStr gn)
    (Nothing, Just gn) -> do 
        updateList (idStr gn:)
        analyzeError id "You can not use constants on the left side"
    (Just fn, Nothing) -> do 
        simps <- fmap conList getContext
        let f = idStr fn
        if f `elem` simps then return () else updateList (f:)
    (Nothing, Nothing) -> analyzeError id "Constants always have the same simplicity"
    where
    funIdent:: Fom -> Maybe Ident
    funIdent fun@FunFom{} = Just $ funName fun
    funIdent _ = Nothing
    insertSimpByName:: String -> String -> Analyzer ()
    insertSimpByName f g = do
        m <- fmap conList getContext
        case (elemIndex f m, elemIndex g m) of
            (Just fi, Just gi) -> when (fi > gi) $ analyzeError id "Not as simple as the left side"
            (Just fi, Nothing) -> updateList $ insertAt g fi
            (Nothing, Just gi) -> updateList $ insertAt f (gi+1)
            (Nothing, Nothing) -> updateList (\m-> g:f:m)
        where
        insertAt:: a -> Int -> [a] -> [a]
        insertAt x 0 as = x:as
        insertAt x i (a:as) = a:insertAt x (i - 1) as

simplify:: Fom -> Analyzer Fom
simplify fom = do
    simp <- fmap conSimp getContext
    list <- fmap conList getContext
    return $ simplify' list simp fom

simplify':: Simplicity -> RuleMap -> Fom -> Fom
simplify' simps m e = maybe e (simplify' simps m) $ step e where
    step:: Fom -> Maybe Fom
    step e = applyByHeadList heads e where
        simpCompare a b = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e

    lookupHeads:: Fom -> [(String, Int)]
    lookupHeads rew@Rewrite{} = lookupHeads $ rewLater rew
    lookupHeads fun@FunFom{} = maybe rest (:rest) head where
            f = idStr $ funName fun
            head = elemIndex f simps >>= Just . (f, )
            rest = concatMap lookupHeads (funArgs fun)
    lookupHeads _ = []

    apply:: [Rule] -> Fom -> Maybe Fom
    apply (rule:rules) trg = case unify (ruleBf rule) trg of
        Just asg -> Just $ Rewrite (NormalReason rule asg) (assign asg (ruleAf rule)) trg
        Nothing -> apply rules trg
    apply [] _ = Nothing

    applyAtSimp:: [Rule] -> Int -> Fom -> Maybe Fom
    applyAtSimp rules simp (Rewrite r a b) = applyAtSimp rules simp a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rules simp fun@FunFom{} = do
        fsimp <- elemIndex (idStr $ funName fun) simps
        let rest = applyArgsOnce (applyAtSimp rules simp) fun
        if simp == fsimp then apply rules e <|> rest else rest
    applyAtSimp _ _ _ = Nothing

    applyByHeadList:: [(String, Int)] -> Fom -> Maybe Fom
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList xs e

type Derivater = (Fom, Fom) -> Analyzer (Maybe Fom)
applyDiff:: Derivater -> (Fom, Fom) -> Analyzer (Maybe Fom)
applyDiff derivater pair@(fun@(FunFom _ ty f as), FunFom _ ty' g bs) = if f == g && length as == length bs
    then case num of
        0 -> return Nothing
        1 -> do
            let (xs', x:xs) = splitAt idx args
            res <- derivater x
            return $ (\t-> fun{funArgs=map snd xs' ++ t:map snd xs}) <$> res
        _ -> derivater pair
    else derivater pair where
        args = zip as bs
        es = fmap (uncurry (==)) args
        (idx, num) = encount False es
        -- (element, list) -> (index of the first encountered element, number of encounters)
        encount:: Eq a => a -> [a] -> (Int, Int)
        encount = encount' (-1, 0) where
            encount':: Eq a => (Int, Int) -> a -> [a] -> (Int, Int)
            encount' (i, n) e (x:xs) = encount' (if n > 0 then i else i + 1, if e == x then n + 1 else n) e xs
            encount' p _ [] = p

derivate:: Derivater
derivate = applyDiff derivateByRuleList where
    derivateByRuleList:: Derivater
    derivateByRuleList pair@(FunFom _ h ty as, goal) = do
        rmap <- fmap conImpl getContext
        let mRules = M.lookup (idStr h) rmap
        case mRules of
            Just rules -> derivateByRules rules pair
                where
                derivateByRules:: [Rule] -> Derivater
                derivateByRules [] pair = return Nothing
                derivateByRules (x:xs) pair = do
                    a <- derivateByRule x pair
                    b <- derivateByRules xs pair
                    return $ a <|> b
            Nothing -> return Nothing
    derivateByRuleList _ = return Nothing
    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' rule (begin, goal) = do
            let mAsg = unify (ruleBf rule) begin
            case mAsg of
                Just asg -> return $ if assign asg (ruleAf rule) == goal 
                    then Just $ Rewrite (NormalReason rule asg) goal begin
                    else Nothing
                Nothing -> return Nothing

derivateExists:: Derivater
derivateExists = applyDiff derivateExists where
    contains:: Eq a => [a] -> [a] -> Bool
    contains [] _ = True
    contains (x:xs) set = x `elem` set && contains xs set
    derivateExists:: Derivater
    derivateExists (fom, var@(VarFom id varTy)) = do
        vmap <- fmap conVar getContext 
        case M.lookup (idStr id) vmap of
            (Just (Variable (Exists refs) ty)) -> if ty == varTy && contains ids refs 
                then return $ Just var
                else return Nothing
            _ -> return $ if fom == var then Just var else Nothing
        where
        ids = lookupVars fom
    derivateExists (_, goal) = return $ Just goal

derivateUnfold:: Derivater
derivateUnfold = applyDiff unfold where
    unfold:: Derivater
    unfold (trg@(VarFom id UnknownFom), VarFom _ ty) = do
        insertEnt False id ty
        return $ Just trg
    unfold (trg@(VarFom _ trgTy), VarFom _ defTy) = return $ if trgTy == defTy then Just trg else Nothing
    unfold (trg@FunFom{}, def@FunFom{}) = if funName trg == funName def
        then do
            mArgs <- mapM unfold $ zip (funArgs trg) (funArgs def)
            return $ maybe Nothing (\args-> Just trg{funArgs=args}) $ conjMaybe mArgs
        else return Nothing
    unfold (trg, def) = return $ if trg == def then Just trg else Nothing

mergeRewrite:: Fom -> Fom -> Maybe Fom
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, Fom, Reason) -> Fom -> Fom -> Maybe Fom
    mergeRewrite junction former@(Rewrite r a b) latter@(Rewrite r' a' b') = if a == a'
        then mergeRewrite (Just (r, a, r')) b b'
        else case junction of
            Just (jr, je, jr') -> Just $ appendStep jr' (Rewrite jr je former) latter 
            Nothing -> Nothing
    mergeRewrite _ former latter@(Rewrite r a b) = if former == a
        then mergeRewrite Nothing former a >>= \x-> Just $ appendStep r x b
        else Nothing
    mergeRewrite _ former@(Rewrite r a b) latter = if a == latter
        then mergeRewrite Nothing a latter >>= \x-> Just $ Rewrite r x b
        else Nothing
    mergeRewrite _ funA@FunFom{} funB@FunFom{} = if funName funA == funName funB
        then (\x-> funA{funArgs=x}) <$> conjMaybe (zipWith (mergeRewrite Nothing) (funArgs funA) (funArgs funB))
        else Nothing
    mergeRewrite _ a b = if a == b then Just a else Nothing

    appendStep:: Reason -> Fom -> Fom -> Fom
    appendStep r' t (Rewrite r a b) = Rewrite r a (appendStep r' t b)
    appendStep r t u = Rewrite r u t

lookupVars:: Fom -> [Ident]
lookupVars fun@FunFom{} = concatMap lookupVars $ funArgs fun
lookupVars (VarFom id _) = [id]
lookupVars _ = []