module Rewriter(unify, assign, simplify, insertSimp, mergeRewrite) where
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

unify:: Formula -> Formula -> Maybe AssignMap
unify ptn trg = unifym ptn trg M.empty

unifym:: Formula -> Formula -> AssignMap -> Maybe AssignMap
unifym Rewrite{} _ = const $ error "Do not use Rewrite in a rule"
unifym ptn trg@Rewrite{} = unifym ptn $ later trg
unifym TypeOfType TypeOfType = id . Just
unifym ptnWhole@(Formula ptnBody ptnType) trgWhole@(Formula trgBody trgType) = \m-> do
    typeAsg <- unifym ptnType trgType m
    bodyAsg <- unifyBody ptnBody trgBody typeAsg
    return $ M.union typeAsg bodyAsg
    where
    toUnify:: Bool -> AssignMap -> Maybe AssignMap
    toUnify cond = \m-> if cond then Just m else Nothing

    unifyBody:: FormulaBody -> FormulaBody -> AssignMap -> Maybe AssignMap
    unifyBody ptn@CstFormula{} trg = toUnify $ ptn == trg
    unifyBody ptn@NumFormula{} trg = toUnify $ ptn == trg
    unifyBody ptn@StrFormula{} trg = toUnify $ ptn == trg

    unifyBody ptn@(VarFormula id) trg = \m-> case M.lookup (idStr id) m of
        Just x -> if fomBody x == trg then Just m else Nothing
        Nothing -> Just $ M.insert (idStr id) (latestFormula trgWhole) m

    unifyBody (FunFormula OFun f ax) (FunFormula OFun f' ax') = 
        if f == f' then unifyArgs ax ax' else const Nothing
        where
        unifyArgs:: [Formula] -> [Formula] -> AssignMap -> Maybe AssignMap
        unifyArgs (e:ex) (e':ex') = unifym e e' <&&> unifyArgs ex ex'
        unifyArgs [] [] = id . Just
        unifyArgs _ _ = const Nothing

    unifyBody (FunFormula (ACFun rest) f ax) (FunFormula (ACFun rest') f' ax') =
        if f == f' then match ax ax' else const Nothing
        where
        match:: [Formula] -> [Formula] -> AssignMap -> Maybe AssignMap
        match [] trgs = Just . M.insert rest (Formula (FunFormula (ACFun "") f trgs) trgType)
        match (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs where

        matchForPtn:: Formula -> [Formula] -> [Formula] -> [Formula] -> AssignMap -> Maybe AssignMap
        matchForPtn ptn ptns noMatchTrgs [] = const Nothing
        matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
            main = unifym ptn trg <&&> match ptns (noMatchTrgs ++ restTrgs)
            rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs

    unifyBody _ _ = const Nothing

    (<||>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
    a <||> b = \m-> a m <|> b m
    (<&&>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
    a <&&> b = \m-> a m >>= \m'-> b m'

assign:: AssignMap -> Formula -> Formula
assign m fom@(Formula (VarFormula id) etype) = fromMaybe fom $ M.lookup (idStr id) m
assign m fom = applyArgs (assign m) fom

insertSimp:: Ident -> Formula -> Formula -> Analyzer ()
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

applyArgsOnce:: (Formula -> Maybe Formula) -> Formula -> Maybe Formula
applyArgsOnce f (Formula fom _) = applyArgsOnce' (funArgs fom) [] >>= \args-> fom{funArgs=args} where
    applyArgsOnce':: [Formula] -> [Formula] -> Maybe [Formula]
    applyArgsOnce' [] _ = Nothing
    applyArgsOnce' (a:as) as' = maybe (applyArgsOnce' as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (f a)

simplify:: Simplicity -> RuleMap -> Formula -> Formula
simplify simps m e = maybe e (simplify simps m) $ step e where
    step:: Formula -> Maybe Formula
    step e = applyByHeadList heads e where
        simpCompare a b = a `compare` b
        heads = sortBy simpCompare $ lookupHeads e

    lookupHeads:: Formula -> [(String, Int)]
    lookupHeads rew@Rewrite{} = lookupHeads $ later rew
    lookupHeads (Formula (FunFormula _ fun args) _) = maybe rest (:rest) head where
            head = elemIndex (idStr fun) simps >>= Just . (idStr fun, )
            rest = concatMap lookupHeads args
    lookupHeads _ = []

    apply:: [Rule] -> Formula -> Maybe Formula
    apply (rule@(a, b):rules) e = maybe (apply rules e) (\m-> Just $ Rewrite (StepReason rule m) (assign m b) e) (unify a e)
    apply [] _ = Nothing

    applyAtSimp:: [Rule] -> Int -> Formula -> Maybe Formula
    applyAtSimp rules simp (Rewrite r a b) = applyAtSimp rules simp a >>= \x-> Just $ Rewrite r x b
    applyAtSimp rules simp fom@(Formula FunFormula{} etype) = do
        fsimp <- elemIndex (idStr fun) simps
        let rest = applyArgsOnce (applyAtSimp rules simp) fom
        if simp == fsimp then apply rules e <|> rest else rest
    applyAtSimp _ _ _ = Nothing

    applyByHeadList:: [(String, Int)] -> Formula -> Maybe Formula
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList xs e

type Derivater = (Formula, Formula) -> Maybe Formula
derivate:: RuleMap -> (Formula, Formula) -> Maybe Formula
derivate m = applyDiff derivateByRuleList where
    applyDiff:: Derivater -> (Formula, Formula) -> Maybe Formula
    applyDiff d pair@(fom@(Formula (FunFormula _ f as) _), Formula (FunFormula _ g bs) _) = if f == g && length as == length bs
        then case num of
            0 -> Nothing
            1 -> derivate m x >>= \t-> Just $ changeArgs fom (map snd xs' ++ t:map snd xs) where
                (xs', x:xs) = splitAt idx args
            _ -> d pair
        else d pair where
            args = zip as bs
            es = fmap (uncurry (==)) args
            (idx, num) = encount False es
            -- (element, list) -> (index of the first encountered element, number of encounters)
            encount:: Eq a => a -> [a] -> (Int, Int)
            encount = encount' (-1, 0) where
                encount':: Eq a => (Int, Int) -> a -> [a] -> (Int, Int)
                encount' (i, n) e (x:xs) = encount' (if n > 0 then i else i + 1, if e == x then n + 1 else n) e xs
                encount' p _ [] = p
    applyDiff d pair = d pair

    derivateByRuleList:: Derivater
    derivateByRuleList pair@(Formula (FunFormula _ h as) _, goal) = M.lookup (show h) m 
        >>= foldr ((<|>) . flip derivateByRule pair) Nothing
    derivateByRuleList _ = Nothing

    derivateByRule:: Rule -> Derivater
    derivateByRule d = applyDiff $ derivate' d where
        derivate':: Rule -> Derivater
        derivate' r@(ra, rb) (ta, tb) = unify ra ta >>= \m-> if assign m rb == tb 
            then Just $ Rewrite (ImplReason r m) tb ta
            else Nothing

mergeRewrite:: Formula -> Formula -> Maybe Formula
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, Formula, Reason) -> Formula -> Formula -> Maybe Formula
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
    mergeRewrite _ fom@(Formula (FunFormula ftype f as) _) (Formula (FunFormula _ g bs) _) = if f == g
        then changeArgs fom <$> conjMaybe (zipWith (mergeRewrite Nothing) as bs)
        else Nothing
    mergeRewrite _ a b = if a == b then Just a else Nothing

    appendStep:: Reason -> Formula -> Formula -> Formula
    appendStep r' t (Rewrite r a b) = Rewrite r a (appendStep r' t b)
    appendStep r t u = Rewrite r u t
