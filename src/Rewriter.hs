module Rewriter where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Library
import Data
import Visualizer

instance Eq Fom where
    a@FunFom{} == b@FunFom{} = sameAttr && case (funAttr a, funAttr b) of
            (ACFun{}, _) -> equalACFun a b
            (_, ACFun{}) -> equalACFun a b
            _ -> funArgs a == funArgs b
        where
        sameAttr:: Bool
        sameAttr = funName a == funName b && funType a == funType b
        equalACFun:: Fom -> Fom -> Bool
        equalACFun a b = equalAsSet (funArgs a) (funArgs b) where
    (PredFom vl ty) == (PredFom vl' ty') = vl == vl' && ty == ty'
    (FunTypeFom id args ret) == (FunTypeFom id' args' ret') = id == id' && args == args' && ret == ret'
    (CstFom a x) == (CstFom b y) = a == b && x == y
    (VarFom a x) == (VarFom b y) = a == b && x == y
    (StrFom a) == (StrFom b) = a == b
    (NumFom a) == (NumFom b) = a == b
    TypeOfType == TypeOfType = True
    UnknownFom == UnknownFom = True
    a == b = False

normalizeACRewrite:: Fom -> Fom
normalizeACRewrite rew@(Rewrite res trg old) = case normalizeACRewrite trg of
    (Rewrite newRes new _)-> Rewrite newRes new rew
    new -> Rewrite res new old
normalizeACRewrite fun@FunFom{} = if length (filter ((>1) . length) mArgs) >= 1 
    then Rewrite ACNormalizeReason fun{funArgs=concat mArgs} fun
    else fun{funArgs=nArgs}
    where 
    nArgs = map normalizeACRewrite $ funArgs fun
    mArgs = map applyArg nArgs
    applyArg:: Fom -> [Fom]
    applyArg rew@Rewrite{} = case latestFom rew of
        rewFun@FunFom{} -> if funName fun == funName rewFun then funArgs rewFun else [rewFun]
        latest -> [latest]
    applyArg arg = [arg]
normalizeACRewrite fom = fom

(<||>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
a <||> b = \m-> a m <|> b m

extractArgs:: String -> Fom -> [Fom]
extractArgs str fun@FunFom{} = if str == idStr (funName fun)
    then concatMap (extractArgs str) (funArgs fun)
    else [fun]
extractArgs str fom = [fom]

convert:: Fom -> Fom -> Analyzer Bool
convert from to = if from == to 
    then return True
    else do
        fromEnt <- lookupEnt (idStr $ showIdent from)
        toEnt <- lookupEnt (idStr $ showIdent to)
        fromMaybe (return False) $ cast to <$> fromEnt <*> toEnt
    where
    cast:: Fom -> Entity -> Entity -> Analyzer Bool
    cast trg from to = case (entPred from, entPred to) of
        (Just pred, Nothing) -> return $ varStr pred == (idStr $ entName to)
        (Nothing, Just pred) -> do
            rules <- lookupPredRules (varStr pred) (idStr $ showIdent trg)
            case unifyList predRuleTrg rules trg of
                Just (asg, rule) -> return True
                Nothing -> return False

unify:: Fom -> Fom -> Maybe AssignMap
unify ptn trg = unifyWithAsg ptn trg M.empty

unifyFun:: ([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyFun unifyArgs ptn trg = if funName ptn /= funName trg then const Nothing else \m-> do
    tyAsg <- unifyWithAsg (funType ptn) (funType trg) m
    vlAsg <- unifyArgs (funArgs ptn) (funArgs trg) tyAsg
    return $ M.union tyAsg vlAsg

unifyArgsOrder:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyArgsOrder ptns args = if length ptns /= length args 
    then return Nothing
    else unifyArgs ptns args
    where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs (e:ex) (e':ex') = unifyWithAsg e e' >=> unifyArgs ex ex'
    unifyArgs [] [] = Just
    unifyArgs _ _ = const Nothing

unifyArgsRandom:: ([Fom] -> AssignMap -> Maybe AssignMap) -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyArgsRandom restInserter = unifyArgs where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [] rests = restInserter rests
    unifyArgs (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs
    matchForPtn:: Fom -> [Fom] -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    matchForPtn ptn ptns noMatchTrgs [] = const Nothing
    matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
        main = unifyWithAsg ptn trg >=> unifyArgs ptns (noMatchTrgs ++ restTrgs)
        rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs

checkInsert:: String -> Fom -> AssignMap -> Maybe AssignMap
checkInsert name fom = \m-> case M.lookup name m of
    Just x -> if x == fom then Just m else Nothing
    Nothing -> Just $ M.insert name fom m

toFunFom:: AssignMap -> Fom -> Fom
toFunFom m (ACInsertFom isrtName fom) = case M.lookup isrtName m of
    Just fun@FunFom{}
        | funName fun == funName ptn -> ptn{funArgs=(map RawVarFom $ funArgs fun) ++ funArgs ptn}
        | otherwise -> ptn{funArgs=RawVarFom fun:funArgs ptn}
    Just fom -> ptn{funArgs=RawVarFom fom:funArgs ptn}
    where ptn = toFunFom m fom
toFunFom m fom = fom

unifyWithAsg:: Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyWithAsg Rewrite{} _ = const $ error "Do not use Rewrite in a rule"
unifyWithAsg ptn trg@Rewrite{} = unifyWithAsg ptn $ rewLater trg
unifyWithAsg TypeOfType TypeOfType = Just
unifyWithAsg ptn@(CstFom id ty) trg@(CstFom id' ty') = if id == id' then unifyWithAsg ty ty' else const Nothing
unifyWithAsg ptn@NumFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg ptn@StrFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg (PredFom trgVl trgTy) (PredFom ptnVl ptnTy) = unifyWithAsg trgVl ptnVl >=> unifyWithAsg trgTy ptnTy
unifyWithAsg (RawVarFom ptn) trg = if ptn == trg then Just else const Nothing
unifyWithAsg ptn@(VarFom id ty) trg = checkInsert (idStr id) (latestFom trg) 
unifyWithAsg ptn@FunFom{} trg@FunFom{} = case funAttr trg of
    OFun -> unifyFun unifyArgsOrder ptn trg
    CFun -> unifyFun unifyArgsComm ptn trg
    AFun -> unifyFun unifyArgsOrder ptn trg
    ACFun -> unifyFun (unifyArgsRandom $ \case []-> Just; _-> const Nothing) ptn trg
    where
    unifyArgsComm:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgsComm [a, b] [a', b'] = (unifyWithAsg a a' >=> unifyWithAsg b b') <||> (unifyWithAsg a b' >=> unifyWithAsg b a')
unifyWithAsg ptn@ACInsertFom{} trg@FunFom{} = \m-> unifyWithAsg (toFunFom m ptn) trg m
unifyWithAsg (ACRestFom restName ptn) trg@FunFom{} = \m-> unifyFun (unifyArgsRandom inserter) (toFunFom m ptn) trg m where
    inserter [rest] = checkInsert restName rest
    inserter rests = checkInsert restName trg{funArgs=rests}
unifyWithAsg _ _ = const Nothing

unifyList:: (a -> Fom) -> [a] -> Fom -> Maybe (AssignMap, a)
unifyList f (x:xs) trg = case unify (f x) trg of
    Just asg -> Just (asg, x)
    Nothing -> unifyList f xs trg

assign:: AssignMap -> Fom -> Fom
assign m var@(VarFom id ty) = fromMaybe var $ M.lookup (idStr id) m
assign m fun@(FunFom ACFun _ _ _) = case concatMap toArray args of [x]-> x; xs-> fun{funArgs=xs}; where
    args = map (assign m) $ funArgs fun
    toArray arg@FunFom{} = if funName arg == funName fun then funArgs arg else [arg]
    toArray arg = [arg]
assign m fom@FunFom{} = applyArgs (assign m) fom
assign m ACRestFom{} = error "assign m ACRestFom{}"
assign m (ACEachFom name src fun lambda) = case M.lookup name m of 
    Just list -> fun{funArgs=map (applyUnaryLambda lambda m) $ toList list}
    Nothing -> error "not found"
    where
    toList trg@FunFom{} = if src == (idStr $ funName trg) then funArgs trg else [trg]
    toList trg = [trg]
assign m fom = fom

applyUnaryLambda:: UnaryLambda -> AssignMap -> Fom -> Fom
applyUnaryLambda (UnaryLambda arg body) m value = assign (M.insert arg value m) body

insertSimp:: Ident -> Fom -> Fom -> Analyzer ()
insertSimp id a b = case (funIdent a, funIdent b) of
    (Just fn, Just gn) -> insertSimpByName (idStr fn) (idStr gn)
    (Nothing, Just gn) -> analyzeError id "定数は関数よりも常に簡単なため、定数を左辺に使うことはできません"
    (Just fn, Nothing) -> updateList $ \list-> let f = idStr fn in if f `elem` list then list else f:list
    (Nothing, Nothing) -> analyzeError id "全ての定数は等しい簡略性を持つため、定数を両端に持つ命題は無効です"
    where
    funIdent:: Fom -> Maybe Ident
    funIdent (ACRestFom _ fun) = funIdent fun
    funIdent fun@FunFom{} = Just $ funName fun
    funIdent _ = Nothing
    insertSimpByName:: String -> String -> Analyzer ()
    insertSimpByName f g = do
        m <- fmap conList getContext
        case (elemIndex f m, elemIndex g m) of
            (Just fi, Just gi) -> when (fi > gi) $ analyzeError id "すでに宣言された命題から推論した関数の簡略性によると、左辺の方が右辺よりも簡単です"
            (Just fi, Nothing) -> updateList $ insertAt g fi
            (Nothing, Just gi) -> updateList $ insertAt f (gi+1)
            (Nothing, Nothing) -> updateList $ \m-> if f == g then f:m else g:f:m
        where
        insertAt:: a -> Int -> [a] -> [a] 
        insertAt item idx xs = as ++ (item:bs) where (as, bs) = splitAt idx xs

simplify:: Fom -> Analyzer Fom
simplify fom = do
    simp <- fmap conSimp getContext
    list <- fmap conList getContext
    return $ simplifyStepLoop list simp fom

simplifyStepLoop:: Simplicity -> RuleMap -> Fom -> Fom
simplifyStepLoop simps m _fom = maybe _fom (simplifyStepLoop simps m) $ simplifyStepAndNom _fom where
    lookupHeads:: Fom -> [(String, Int)]
    lookupHeads rew@Rewrite{} = lookupHeads $ rewLater rew
    lookupHeads fun@FunFom{} = maybe rest (:rest) head where
            f = idStr $ funName fun
            head = elemIndex f simps >>= Just . (f, )
            rest = concatMap lookupHeads (funArgs fun)
    lookupHeads _ = []
    applyWithSimp:: [Rule] -> Int -> Fom -> Maybe Fom
    applyWithSimp rules simp rew@(Rewrite res trg old) = applyWithSimp rules simp trg >>= \case
        (Rewrite newRes new _)-> Just $ Rewrite newRes new rew -- rewrite whole
        new -> Just $ Rewrite res new old                      -- rewrite argument
    applyWithSimp rules simp fun@FunFom{} = if simp == fsimp then apply rules fun <|> rest else rest where
        fsimp = fromMaybe (-1) $ elemIndex (idStr $ funName fun) simps
        rest = applyArgsOnce (applyWithSimp rules simp) fun
        apply:: [Rule] -> Fom -> Maybe Fom
        apply (rule:rules) trg = case unify (ruleBf rule) trg of
            Just asg -> Just $ Rewrite (NormalReason rule asg) (assign asg (ruleAf rule)) trg
            Nothing -> apply rules trg
        apply [] _ = Nothing
    applyWithSimp _ _ _ = Nothing
    applyByHeadList:: [(String, Int)] -> Fom -> Maybe Fom
    applyByHeadList [] _ = Nothing
    applyByHeadList ((f, s):xs) e = (M.lookup f m >>= \x-> applyWithSimp x s e) <|> applyByHeadList xs e
    simplifyStep:: Fom -> Maybe Fom
    simplifyStep e = applyByHeadList (traceShow heads heads) e where
        simpCompare (_, a) (_, b) = compare b a
        heads = sortBy simpCompare $ nub $ lookupHeads e
    simplifyStepAndNom:: Fom -> Maybe Fom
    simplifyStepAndNom = simplifyStep >=> Just . normalizeACRewrite

type Derivater = (Fom, Fom) -> Analyzer (Maybe Fom)

applyDiff:: Derivater -> (Fom, Fom) -> Analyzer (Maybe Fom)
applyDiff derivater pair@(bg@FunFom{}, gl@FunFom{}) = if funName bg == funName gl && length as == length bs
    then case num of
        0 -> return Nothing
        1 -> do
            let (xs', x:xs) = splitAt idx argPairs
            res <- applyDiff derivater x
            return $ (\t-> bg{funArgs=map snd xs' ++ t:map snd xs}) <$> res
        _ -> do
            let eqDerivate pair@(a, b) = if a == b then return $ Just b else derivater pair
            res <- derivater pair
            argsRes <- conjMaybe <$> mapM eqDerivate argPairs
            return $ (\x-> bg{funArgs=x}) <$> argsRes <|> res
    else derivater pair where
        (as, bs) = (funArgs bg, funArgs gl)
        argPairs = zip as bs
        matchArgs = fmap (uncurry (==)) argPairs
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
        derivateByRule rule (begin, goal) = return $ do
            asgAf <- unify (ruleAf rule) goal
            asg <- unifyWithAsg (ruleBf rule) begin (traceShow asgAf asgAf)
            return $ Rewrite (NormalReason rule asg) goal begin
    derivateByRuleList:: Derivater
    derivateByRuleList pair@(FunFom _ h ty as, goal) = do
        rmap <- fmap conImpl getContext
        let or a b = a >>= \x-> b >>= return . (<|>x)
        case M.lookup (idStr h) rmap of
            Just rules -> foldr (or . flip derivateByRule pair) (return Nothing) rules
            Nothing -> return Nothing
    derivateByRuleList _ = return Nothing

checkUnfold:: EntityMap -> AssignMap -> Fom -> Fom -> Analyzer (Maybe Fom)
checkUnfold defMap argMag = checkUnfold where
    checkUnfold:: Fom -> Fom -> Analyzer (Maybe Fom)
    checkUnfold (VarFom (Ident _ name) ty) gl =
        case (M.lookup name defMap, M.lookup name argMag) of
            (Just defEnt, _) -> do
                mEnt <- lookupEnt name
                case mEnt of
                    Just ent -> return $ if entQtf ent == entQtf defEnt then Just gl else Nothing
                    Nothing -> insertNewVarDec (entType defEnt) (entQtf defEnt) gl
            (_, Just arg) -> return $ if arg == gl then Just gl else Nothing
            (_, _) -> return Nothing
    checkUnfold def@FunFom{} gl@FunFom{} = if funName def == funName gl 
        then do
            mArgs <- mapM (uncurry checkUnfold) (zip (funArgs def) (funArgs gl))
            return $ (\x-> gl{funArgs=x}) <$> (conjMaybe $ mArgs)
        else return Nothing
    checkUnfold def gl = if def == gl then return $ Just gl else return Nothing
    insertNewVarDec:: Fom -> Quantifier -> Fom -> Analyzer (Maybe Fom)
    insertNewVarDec ty ForAll (VarFom id _) = do
        insertEnt id ty
        return $ Just $ VarFom id ty
    -- insertNewVarDec ty ForAll fun@FunFom{} = do
    --     mapM (insertNewVarDec ty ForAll)
    --     fun{funArgs=funArgs fun}
    insertNewVarDec ty ForAll fom = return $ Just fom
    insertNewVarDec ty qtf@Exists{} var@(VarFom id _) = do
        insertEntMap id ty $ \ent-> ent{entQtf=qtf}
        return $ Just $ VarFom id ty
    insertNewVarDec _ _ _ = return Nothing

derivateUnfold:: Derivater
derivateUnfold = applyDiff unfold where
    getMaybe (Just (Just x)) = Just x
    getMaybe _ = Nothing
    unfold:: Derivater
    unfold (bg@FunFom{}, gl) = do
        mEnt <- lookupEnt (idStr $ funName bg)
        case (mEnt, entDef <$> mEnt) of
            (Just ent, Just (Just def)) -> do
                let argAsg = M.fromList $ zip (defArgs def) (funArgs bg)
                checkUnfold (defScope def) argAsg (defBody def) gl
            _ -> return Nothing
    unfold _ = return Nothing

derivateFold:: Derivater
derivateFold = applyDiff fold where
    fold:: Derivater
    fold (bg, gl@FunFom{}) = do
        mEnt <- lookupEnt (idStr $ funName gl)
        case (mEnt, entDef <$> mEnt) of
            (Just ent, Just (Just def)) -> do
                let argAsg = M.fromList $ zip (defArgs def) (funArgs gl)
                res <- checkUnfold (defScope def) argAsg (defBody def) bg
                return $ maybe (Just gl) (const $ Just gl) res
            _ -> return Nothing

mergeRewrite:: Fom -> Fom -> Maybe Fom
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, Fom, Reason) -> Fom -> Fom -> Maybe Fom
    mergeRewrite junction former@(Rewrite r a b) latter@(Rewrite r' a' b') = case mergeRewrite junction a a' of
        Just res -> Just $ if hasRewrite res then app else fromMaybe app $ mergeRewrite (Just (r, a, r')) b b' 
            where app = appendStep r' (Rewrite r res b) b'
        Nothing  -> junction >>= \(jr, je, jr') -> Just $ appendStep jr' (Rewrite jr je former) latter 
    mergeRewrite _ former latter@(Rewrite r a b) = mergeRewrite Nothing former a >>= \x-> Just $ appendStep r x b
    mergeRewrite _ former@(Rewrite r a b) latter = mergeRewrite Nothing a latter >>= \x-> Just $ Rewrite r x b
    mergeRewrite _ funA@FunFom{} funB@FunFom{} = if funName funA == funName funB
        then do
            let zipFunc = if funAttr funA == ACFun then zipRandomFom else \x y-> Just $ zip x y
            argPairs <- zipFunc (funArgs funA) (funArgs funB)
            let merges = map (uncurry $ mergeRewrite Nothing) argPairs
            conjMerge <- conjMaybe merges
            return funA{funArgs=conjMerge}
        else Nothing
    mergeRewrite _ a b = if a == b then Just a else Nothing
    appendStep:: Reason -> Fom -> Fom -> Fom
    appendStep juncRes trg (Rewrite r a b) = appendStep r (Rewrite juncRes a trg) b
    appendStep juncRes trg new = Rewrite juncRes new trg
    hasRewrite:: Fom -> Bool
    hasRewrite Rewrite{} = True
    hasRewrite fun@FunFom{} = all hasRewrite $ funArgs fun
    hasRewrite _ = False
    zipRandomFom:: [Fom] -> [Fom] -> Maybe [(Fom, Fom)]
    zipRandomFom = zipRandom (\x y-> latestFom x == latestFom y)
    zipRandom:: (a -> a -> Bool) -> [a] -> [a] -> Maybe [(a, a)]
    zipRandom equals as bs = if length as == length bs then zipRandom equals as bs else Nothing where
        zipRandom:: (a -> a -> Bool) -> [a] -> [a] -> Maybe [(a, a)]
        zipRandom f [] [] = Just []
        zipRandom f (a:as) bs = case splitWith f a bs of 
            Just (x, xs) -> ((a, x):) <$> zipRandom f as xs
            Nothing -> Nothing
        splitWith:: (a -> a -> Bool) -> a -> [a] -> Maybe (a, [a])
        splitWith f it [] = Nothing
        splitWith f it (x:xs) = if f it x then Just (x, xs) else (fmap (x:)) <$> splitWith f it xs

lookupVars:: Fom -> [Ident]
lookupVars fun@FunFom{} = concatMap lookupVars $ funArgs fun
lookupVars (VarFom id _) = [id]
lookupVars _ = []