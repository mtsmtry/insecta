module Rewriter where
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
a <&&> b = a >=> b

extractArgs:: String -> Fom -> [Fom]
extractArgs str fun@FunFom{} = if str == idStr (funName fun)
    then concatMap (extractArgs str) (funArgs fun)
    else [fun]
extractArgs str expr = [expr]

convert:: Fom -> Fom -> Analyzer Bool
convert from to = if from == to 
    then return True
    else do
        fromEnt <- lookupEnt (idStr $ showIdent from)
        toEnt <- lookupEnt (idStr $ showIdent to)
        fromMaybe (return False) $ cast to <$> fromEnt <*> toEnt
    where
    cast:: Fom -> Entity -> Entity -> Analyzer Bool
    cast trg from@PredEntity{} to@Entity{} = return $ predExtend from == trg
    cast trg from@Entity{} to@PredEntity{} = do
        rules <- lookupPredRules (predName to) (idStr $ showIdent trg)
        case unifyList predRuleTrg rules trg of
            Just (asg, rule) -> return True
            Nothing -> return False

unify:: Fom -> Fom -> Maybe AssignMap
unify ptn trg = unifyWithAsg ptn trg M.empty

unifyFun:: ([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyFun unifyArgs ptn trg ptns trgs = if funName ptn /= funName trg then const Nothing else \m-> do
    tyAsg <- unifyWithAsg (funType ptn) (funType trg) m
    vlAsg <- unifyArgs ptns trgs tyAsg
    return $ M.union tyAsg vlAsg

unifyFunExtract::([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyFunExtract unifyArgs ptn trg = unifyFun unifyArgs ptn trg ptns trgs where
    name = idStr $ funName ptn
    ptns = extractArgs name ptn
    trgs = extractArgs name trg

unifyFunNormal::([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyFunNormal unifyArgs ptn trg = unifyFun unifyArgs ptn trg (funArgs ptn) (funArgs trg)

unifyArgsOrder:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyArgsOrder ptns args = if length ptns /= length args 
    then return Nothing
    else unifyArgs ptns args
    where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs (e:ex) (e':ex') = unifyWithAsg e e' <&&> unifyArgs ex ex'
    unifyArgs [] [] = Just
    unifyArgs _ _ = const Nothing

unifyWithAsg:: Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyWithAsg Rewrite{} _ = const $ error "Do not use Rewrite in a rule"
unifyWithAsg ptn trg@Rewrite{} = unifyWithAsg ptn $ rewLater trg
unifyWithAsg TypeOfType TypeOfType = Just
unifyWithAsg ptn@(CstFom id ty) trg@(CstFom id' ty') = if id == id' then unifyWithAsg ty ty' else const Nothing
unifyWithAsg ptn@NumFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg ptn@StrFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg (PredFom trgVl trgTy) (PredFom ptnVl ptnTy) = unifyWithAsg trgVl ptnVl <&&> unifyWithAsg trgTy ptnTy

unifyWithAsg ptn@(VarFom id ty) trg = \m-> case M.lookup (idStr id) m of
    Just x -> if x == trg then Just m else Nothing
    Nothing -> Just $ M.insert (idStr id) (latestFom trg) m

unifyWithAsg ptn@(FunFom OFun _ _ _) trg@(FunFom OFun _ _ _) = unifyFunNormal unifyArgsOrder ptn trg
unifyWithAsg ptn@(FunFom AFun _ _ _) trg@(FunFom AFun _ _ _) = unifyFunExtract unifyArgsOrder ptn trg

unifyWithAsg ptn@(FunFom CFun _ _ _) trg@(FunFom CFun _ _ _) = unifyFunNormal unifyArgs ptn trg where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [a, b] [a', b'] = (unifyWithAsg a a' <&&> unifyWithAsg b b') <||> (unifyWithAsg a b' <&&> unifyWithAsg b a')

unifyWithAsg ptn@(FunFom (ACFun restName) _ _ _) trg@(FunFom (ACFun _) _ _ _) = unifyFunExtract unifyArgs ptn trg where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [] [] = Just
    unifyArgs [] trgs = Just . M.insert restName trg{funArgs=trgs}
    unifyArgs (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs
    matchForPtn:: Fom -> [Fom] -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    matchForPtn ptn ptns noMatchTrgs [] = const Nothing
    matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
        main = unifyWithAsg ptn trg <&&> unifyArgs ptns (noMatchTrgs ++ restTrgs)
        rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs

unifyWithAsg _ _ = const Nothing

unifyList:: (a -> Fom) -> [a] -> Fom -> Maybe (AssignMap, a)
unifyList f (x:xs) trg = case unify (f x) trg of
    Just asg -> Just (asg, x)
    Nothing -> unifyList f xs trg

assign:: AssignMap -> Fom -> Fom
assign m fom@(VarFom id ty) = fromMaybe fom $ M.lookup (idStr id) m
assign m fom@(FunFom (ACFun name) _ _ args@(x:xs)) = case M.lookup name m of
    Just rest -> fom{funArgs=[main, rest]}
    Nothing -> main
    where
    main = if null xs then assign m x else applyArgs (assign m) fom
assign m fom@FunFom{} = applyArgs (assign m) fom
assign m fom = fom

insertSimp:: Ident -> Fom -> Fom -> Analyzer ()
insertSimp id a b = case (funIdent a, funIdent b) of
    (Just fn, Just gn) -> insertSimpByName (idStr fn) (idStr gn)
    (Nothing, Just gn) -> do 
        updateList (idStr gn:)
        analyzeError id "定数は関数よりも常に簡単なため、定数を左辺に使うことはできません"
    (Just fn, Nothing) -> do 
        simps <- fmap conList getContext
        let f = idStr fn
        if f `elem` simps then return () else updateList (f:)
    (Nothing, Nothing) -> analyzeError id "全ての定数は等しい簡略性を持つため、定数を両端に持つルールは無効です"
    where
    funIdent:: Fom -> Maybe Ident
    funIdent fun@FunFom{} = Just $ funName fun
    funIdent _ = Nothing
    insertSimpByName:: String -> String -> Analyzer ()
    insertSimpByName f g = do
        m <- fmap conList getContext
        case (elemIndex f m, elemIndex g m) of
            (Just fi, Just gi) -> when (fi > gi) $ analyzeError id "すでに宣言されたルールから推論した関数の簡略性によると、左辺の方が右辺よりも簡単です"
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
    return $ stepLoop list simp fom

stepLoop:: Simplicity -> RuleMap -> Fom -> Fom
stepLoop simps m _fom = maybe _fom (stepLoop simps m) $ step _fom where
    -- 式 -> [(関数名, 関数の簡略性)]
    lookupHeads:: Fom -> [(String, Int)]
    lookupHeads rew@Rewrite{} = lookupHeads $ rewLater rew
    lookupHeads fun@FunFom{} = maybe rest (:rest) head where
            f = idStr $ funName fun
            head = elemIndex f simps >>= Just . (f, )
            rest = concatMap lookupHeads (funArgs fun)
    lookupHeads _ = []
    -- [ルール] -> 式 -> 結果
    apply:: [Rule] -> Fom -> Maybe Fom
    apply (rule:rules) trg = case unify (ruleBf rule) trg of
        Just asg -> Just $ Rewrite (NormalReason rule asg) (assign asg (ruleAf rule)) trg
        Nothing -> apply rules trg
    apply [] _ = Nothing
    -- [ルール] -> 簡略性 -> 式 -> 結果
    applyAtSimp:: [Rule] -> Int -> Fom -> Maybe Fom
    applyAtSimp rules simp (Rewrite r a b) = applyAtSimp rules simp a
    applyAtSimp rules simp fun@FunFom{} = if simp == fsimp then apply rules fun <|> rest else rest where
        fsimp = fromMaybe (-1) $ elemIndex (idStr $ funName fun) simps
        rest = applyArgsOnce (applyAtSimp rules simp) fun
    applyAtSimp _ _ _ = Nothing
    -- [(関数名, 簡略性)] -> 式 -> 結果
    applyByHeadList:: [(String, Int)] -> Fom -> Maybe Fom
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyAtSimp x s e) <|> applyByHeadList xs e
    -- 式 -> 結果
    step:: Fom -> Maybe Fom
    step e = applyByHeadList heads e where
        simpCompare (_, a) (_, b) = compare a b
        heads = sortBy simpCompare $ lookupHeads e

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
        matchArgs = fmap (uncurry (==)) args
        (idx, num) = encount False matchArgs
        -- (element, list) -> (index of the first encountered element, number of encounters)
        encount:: Eq a => a -> [a] -> (Int, Int)
        encount = encount' (-1, 0) where
            encount':: Eq a => (Int, Int) -> a -> [a] -> (Int, Int)
            encount' (i, n) e (x:xs) = encount' (if n > 0 then i else i + 1, if e == x then n + 1 else n) e xs
            encount' p _ [] = p
applyDiff derivater (a, b) = derivater (a, b)

derivate:: Derivater
derivate = applyDiff derivateByRuleList where
    derivateByRule:: Rule -> Derivater
    derivateByRule rule = applyDiff $ derivateByRule rule where
        derivateByRule:: Rule -> Derivater
        derivateByRule rule (begin, goal) = do
            let mAsg = unify (ruleBf rule) begin
            case mAsg of
                Just asg -> return $ if assign asg (ruleAf rule) == goal 
                    then Just $ Rewrite (NormalReason rule asg) goal begin
                    else Nothing
                Nothing -> return Nothing
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