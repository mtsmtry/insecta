module Kernel.Rewriter where
import Kernel.Data
import Kernel.Basis
import Common.Data
import Common.Utility
import qualified Data.Map as M

normalizeACRewrite:: RewFom -> RewFom
normalizeACRewrite rew@(Rewrite res trg old) = case normalizeACRewrite trg of
    (Rewrite newRes new _)-> Rewrite newRes new rew
    new -> Rewrite res new old
normalizeACRewrite (RewFom fun@FunFom{}) = if length (filter ((>1) . length) mArgs) >= 1 
    then Rewrite ACNormalizeReason (RewFom fun{funArgs=concat mArgs}) fun
    else RewFom fun{funArgs=nArgs}
    where 
    nArgs = map normalizeACRewrite $ funArgs fun
    mArgs = map applyArg nArgs
    applyArg:: RewFom -> [RewFom]
    applyArg rew@Rewrite{} = case latestFom rew of
        (Fom rewFun@FunFom{}) -> if funId fun == funId rewFun then funArgs rewFun else [rewFun]
        latest -> [latest]
    applyArg arg = [arg]
normalizeACRewrite fom = fom

extractArgs:: String -> Fom -> [Fom]
extractArgs str fun@FunFom{} = if str == idStr (funIdent fun)
    then concatMap (extractArgs str) (funArgs fun)
    else [fun]
extractArgs str fom = [fom]

convert:: Fom -> Fom -> ProofAnalyzer Bool
convert from to = if from == to 
    then return True
    else do
        fromEnt <- lookupEnt (idStr $ showIdent from)
        toEnt <- lookupEnt (idStr $ showIdent to)
        fromMaybe (return False) $ cast to <$> fromEnt <*> toEnt
    where
    cast:: Fom -> Symbol -> Symbol -> ProofAnalyzer Bool
    cast trg from to = case (entPred from, entPred to) of
        (Just pred, Nothing) -> return $ varName pred == entName to
        (Nothing, Just pred) -> do
            rules <- lookupPredRules (idStr $ varName pred) (idStr $ showIdent trg)
            case unifyList ruleBf rules trg of
                Just (asg, rule) -> return True
                Nothing -> return False

insertSimp:: Ident -> Fom -> Fom -> ProofAnalyzer ()
insertSimp id a b = case (fomFunIdent a, fomFunIdent b) of
    (Just fn, Just gn) -> insertSimpByName fn gn
    (Just fn, Nothing) -> updateList $ \list-> let f = idStr fn in if f `elem` list then list else f:list
    (Nothing, Just gn) -> analyzeError id "定数は関数よりも常に簡単なため、定数を左辺に使うことはできません"
    (Nothing, Nothing) -> analyzeError id "全ての定数は等しい簡略性を持つため、定数を両端に持つ命題は無効です"
    where
    fomFunIdent:: Fom -> Maybe Ident
    fomFunIdent (ACRestFom _ fun) = fomFunIdent fun
    fomFunIdent fun@FunFom{} = Just $ funIdent fun
    fomFunIdent _ = Nothing
    insertSimpByName:: Ident -> Ident -> ProofAnalyzer ()
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

simplify:: Fom -> ProofAnalyzer Fom
simplify fom = do
    simp <- fmap conSimp getContext
    list <- fmap conList getContext
    return $ simplifyStepLoop list simp fom

simplifyStepLoop:: Simplicity -> RuleMap -> Fom -> Fom
simplifyStepLoop simps m _fom = maybe _fom (simplifyStepLoop simps m) $ simplifyStepAndNom _fom where
    lookupHeads:: Fom -> [(String, Int)]
    lookupHeads rew@Rewrite{} = lookupHeads $ rewLater rew
    lookupHeads fun@FunFom{} = maybe rest (:rest) head where
            f = idStr $ funIdent fun
            head = elemIndex f simps >>= Just . (f, )
            rest = concatMap lookupHeads (funArgs fun)
    lookupHeads _ = []
    applyWithSimp:: [Rule] -> Int -> Fom -> Maybe Fom
    applyWithSimp rules simp rew@(Rewrite res trg old) = applyWithSimp rules simp trg >>= \case
        (Rewrite newRes new _)-> Just $ Rewrite newRes new rew -- rewrite whole
        new -> Just $ Rewrite res new old                      -- rewrite argument
    applyWithSimp rules simp (Fom fun@FunFom{}) = if simp == fsimp then apply rules fun <|> rest else rest where
        fsimp = fromMaybe (-1) $ elemIndex (funId fun) simps
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
    simplifyStep e = applyByHeadList heads e where
        simpCompare (_, a) (_, b) = compare b a
        heads = sortBy simpCompare $ nub $ lookupHeads e
    simplifyStepAndNom:: Fom -> Maybe Fom
    simplifyStepAndNom = simplifyStep >=> Just . normalizeACRewrite

type Derivater = (Fom, Fom) -> ProofAnalyzer (Maybe Fom)

applyDiff:: Derivater -> (Fom, Fom) -> ProofAnalyzer (Maybe Fom)
applyDiff derivater pair@(Fom bg@FunFom{}, Fom gl@FunFom{}) = 
    if funId bg == funId gl && length as == length bs
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
            asg <- unifyWithAsg (ruleBf rule) begin asgAf
            return $ Rewrite (NormalReason rule asg) goal begin
    derivateByRuleList:: Derivater
    derivateByRuleList pair@(FunFom _ h ty as, goal) = do
        rmap <- fmap conImpl getContext
        let or a b = a >>= \x-> b >>= return . (<|>x)
        case M.lookup (idStr h) rmap of
            Just rules -> foldr (or . flip derivateByRule pair) (return Nothing) rules
            Nothing -> return Nothing
    derivateByRuleList _ = return Nothing

checkUnfold:: SymbolMap -> AssignMap -> Fom -> Fom -> ProofAnalyzer (Maybe Fom)
checkUnfold defMap argMag = checkUnfold where
    checkUnfold:: Fom -> Fom -> ProofAnalyzer (Maybe Fom)
    checkUnfold (Fom (VarFom name ty)) gl =
        case (M.lookup name defMap, M.lookup name argMag) of
            (Just defEnt, _) -> do
                mEnt <- lookupEnt name
                case mEnt of
                    Just ent -> return $ if entQtf ent == entQtf defEnt then Just gl else Nothing
                    Nothing -> insertNewVarDec (entType defEnt) (entQtf defEnt) gl
            (_, Just arg) -> return $ if arg == gl then Just gl else Nothing
            (_, _) -> return Nothing
    checkUnfold (Fom def@FunFom{}) (Fom gl@FunFom{}) = if funIdent def == funIdent gl 
        then do
            mArgs <- mapM (uncurry checkUnfold) (zip (funArgs def) (funArgs gl))
            return $ (\x-> gl{funArgs=x}) <$> (conjMaybe $ mArgs)
        else return Nothing
    checkUnfold def gl = if def == gl then return $ Just gl else return Nothing
    insertNewVarDec:: Fom -> Quantifier -> Fom -> ProofAnalyzer (Maybe Fom)
    insertNewVarDec ty ForAll (VarFom id _) = do
        insertEnt id ty
        return $ Just $ VarFom id ty
    -- insertNewVarDec ty ForAll fun@FunFom{} = do
    --     mapM (insertNewVarDec ty ForAll)
    --     fun{funArgs=funArgs fun}
    insertNewVarDec ty ForAll fom = return $ Just fom
    insertNewVarDec ty qtf@Exists{} var@(VarFom id _) = do
        insertEntMap id ty -- $ \ent-> ent{entQtf=qtf}
        return $ Just $ VarFom id ty
    insertNewVarDec _ _ _ = return Nothing

derivateUnfold:: Derivater
derivateUnfold = applyDiff unfold where
    getMaybe (Just (Just x)) = Just x
    getMaybe _ = Nothing
    unfold:: Derivater
    unfold (bg@FunFom{}, gl) = do
        mEnt <- lookupEnt (idStr $ funIdent bg)
        case (mEnt, entDef <$> mEnt) of
            (Just ent, Just (Just def)) -> do
                let argAsg = M.fromList $ zip (map (idStr . varName) $ defArgs def) (funArgs bg)
                checkUnfold (defScope def) argAsg (defBody def) gl
            _ -> return Nothing
    unfold _ = return Nothing

derivateFold:: Derivater
derivateFold = applyDiff fold where
    fold:: Derivater
    fold (bg, Fom gl@FunFom{}) = do
        mEnt <- lookupEnt (funId gl)
        case (mEnt, entDef <$> mEnt) of
            (Just ent, Just (Just def)) -> do
                let argAsg = M.fromList $ zip (map varName $ defArgs def) (funArgs gl)
                res <- checkUnfold (defScope def) argAsg (defBody def) bg
                return $ maybe (Just gl) (const $ Just gl) res
            _ -> return Nothing
    fold (bg, Fom gl@(PredFom vl ty)) = return $ Just $ Fom gl

instance Eq RewFom where
    a == b = latestFom a == latestFom b

mergeRewrite:: RewFom -> RewFom -> Maybe RewFom
mergeRewrite = mergeRewrite Nothing where
    mergeRewrite:: Maybe (Reason, RewFom, Reason) -> RewFom -> RewFom -> Maybe RewFom
    mergeRewrite junction former@(Rewrite r a b) latter@(Rewrite r' a' b') = case mergeRewrite junction a a' of
        Just res -> Just $ if hasRewrite res then app else fromMaybe app $ mergeRewrite (Just (r, a, r')) b b' 
            where app = appendStep r' (Rewrite r res b) b'
        Nothing  -> junction >>= \(jr, je, jr') -> Just $ appendStep jr' (Rewrite jr je former) latter 
    mergeRewrite _ former latter@(Rewrite r a b) = mergeRewrite Nothing former a >>= \x-> Just $ appendStep r x b
    mergeRewrite _ former@(Rewrite r a b) latter = mergeRewrite Nothing a latter >>= \x-> Just $ Rewrite r x b
    mergeRewrite _ (RewFom funA@FunFom{}) (RewFom funB@FunFom{}) = if funId funA == funId funB
        then do
            let zipFunc = if funAttr funA == ACFun then zipRandomFom else \x y-> Just $ zip x y
            argPairs <- zipFunc (funArgs funA) (funArgs funB)
            let merges = map (uncurry $ mergeRewrite Nothing) argPairs
            conjMerge <- conjMaybe merges
            return $ RewFom funA{funArgs=conjMerge}
        else Nothing
    mergeRewrite _ fom@(RewFom a) (RewFom b) = if a == b then Just fom else Nothing
    appendStep:: Reason -> RewFom -> RewFom -> RewFom
    appendStep juncRes trg (Rewrite r a b) = appendStep r (Rewrite juncRes a trg) b
    appendStep juncRes trg new = Rewrite juncRes new trg
    hasRewrite:: RewFom -> Bool
    hasRewrite Rewrite{} = True
    hasRewrite (RewFom fun@FunFom{}) = all hasRewrite $ funArgs fun
    hasRewrite _ = False
    zipRandomFom:: [RewFom] -> [RewFom] -> Maybe [(RewFom, RewFom)]
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