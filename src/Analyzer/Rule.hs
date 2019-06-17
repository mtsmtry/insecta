module Analyzer.Rule where
import Kernel.Data

buildRule:: Expr -> Analyzer (Maybe Rule)
buildRule (FunExpr rId@(Ident _ kind) [bf, af]) = do
    bfFom <- buildFom bf
    afFom <- buildFom af
    case kind of
        ":"   -> makePredRule (bfFom, afFom)
        "=>"  -> normalizeImplACRule (bfFom, afFom) >>= checkType "Prop" >>= makeRule ImplRule (bfFom, afFom)
        "<=>" -> normalizeACRule (bfFom, afFom) >>= checkType "Prop" >>= makeRule EqualRule (bfFom, afFom)
        ">>=" -> normalizeACRule (bfFom, afFom) >>= sameType >>= makeRule SimpRule (bfFom, afFom)
        "="   -> normalizeACRule (bfFom, afFom) >>= sameType >>= makeRule EqualRule (bfFom, afFom)
        _     -> analyzeErrorM rId "無効な命題です"
    where
    makePredRule::(Maybe Fom, Maybe Fom) -> Analyzer (Maybe Rule)
    makePredRule (Just vl, Just ty) = do
        when (evalType ty /= TypeOfType) $ analyzeError (showIdent vl) "型ではありません"
        makeRule PredRule (Just vl, Just ty) (Just (vl, ty))
    makeRule:: RuleKind -> (Maybe Fom, Maybe Fom) -> Maybe (Fom, Fom) -> Analyzer (Maybe Rule)
    makeRule kind (Just bf, Just af) (Just (rBf, rAf))= do
        mLabel <- getLabel bf
        return $ mLabel >>= \label-> Just Rule{ 
            ruleKind=kind, ruleIdent=rId, ruleProof=Nothing, ruleLabel=label, ruleBf=rBf, ruleAf=rAf, 
            ruleProp=makeProp kind bf af } 
        where
        makeProp:: RuleKind -> Fom -> Fom -> Fom
        makeProp ImplRule a b = makeBinary "=>" a b
        makeProp _ a b = makeBinary (if evalType a == makeType "Prop" then "<=>" else "=") a b
        getLabel:: Fom -> Analyzer (Maybe String)
        getLabel fun@FunFom{} = return $ Just $ idStr $ showIdent bf
        getLabel fom = analyzeErrorM (showIdent fom) "左辺は関数値である必要があります"
    makeRule _ _ _ = return Nothing

    checkType:: String -> (Maybe Fom, Maybe Fom) -> Analyzer (Maybe (Fom, Fom))
    checkType ty (bf, af) = do
        chBf <- checkType bf
        chAf <- checkType af
        return $ case (chBf, chAf) of (Just af, Just bf)-> Just (af, bf); _-> Nothing
        where
        checkType (Just fom) = if evalType fom == makeType ty 
            then return $ Just fom
            else analyzeErrorM (funIdent fom) "命題ではありません"
        checkType Nothing = return Nothing

    sameType:: (Maybe Fom, Maybe Fom) -> Analyzer (Maybe (Fom, Fom))
    sameType (Just bf, Just af) = if evalType bf == evalType af
        then return $ Just (bf, af)
        else analyzeErrorM rId "両辺の型が一致しません"
    sameType _ = return Nothing

    normalizeACRule:: (Maybe Fom, Maybe Fom) -> Analyzer (Maybe Fom, Maybe Fom)
    normalizeACRule (Just a, Just b) = case isDistributive a b of
        Just (bfFun, afFun, lambda) -> do
            let rBf = applyUnaryLambda lambda M.empty $ ACRestFom "_" bfFun{funArgs=[]}
            let rAf = ACEachFom "_" (idStr $ funIdent bfFun) afFun lambda
            rBf' <- evalStateT (normalizeACRest rBf) []
            return (rBf', Just rAf)
        Nothing -> do
            nomA <- evalStateT (normalizeACRest a) []
            return $ boxACRest (nomA, Just b)
    normalizeACRule pair = return pair

    normalizeImplACRule::  (Maybe Fom, Maybe Fom) -> Analyzer (Maybe Fom, Maybe Fom)
    normalizeImplACRule pair@(Just bf, Just af) = case isACInsert bf af of
        Just (nBf, nAf) -> return (Just nBf, Just nAf)
        Nothing -> normalizeACRule pair
    normalizeImplACRule pair = return pair
    
    normalizeACRest:: Fom -> StateT [String] Analyzer (Maybe Fom)
    normalizeACRest trg = normalizeACRest (makeVarEmergeMap trg) trg where
        normalizeACRest:: M.Map String Int -> Fom -> StateT [String] Analyzer (Maybe Fom)
        normalizeACRest m (ACRestFom rest fun) = do
            nFun <- normalizeACRest m fun
            return $ ACRestFom rest <$> nFun
        normalizeACRest m fun@(FunFom ACFun _ _ _) = do
            acList <- get
            let oneVars = let oneEmergeVars = map fst $ filter ((==1) . snd) $ M.toList $ varEmergeMap (funArgs fun)
                           in filter ((==Just 1) . flip M.lookup m) oneEmergeVars
            let (acInserts, acRests) = classify (`elem` acList) oneVars
            args <- let varDelArgs = filter (not . isVarWithNames oneVars) (funArgs fun)
                     in conjMaybe <$> mapM (normalizeACRest m) varDelArgs
            let acInserted = (\x-> acInsert acInserts fun{funArgs=x}) <$> args
            case acRests of
                [] -> return acInserted
                [var] -> do
                    put $ var:acList
                    return $ ACRestFom var <$> acInserted
                _ -> lift $ analyzeErrorM (funIdent fun) $ show acRests ++ ":AC演算子の余剰項の代入候補となる変数が2つ以上あり、代入方法が決定不能です"
        normalizeACRest m fun@FunFom{} = do
            args <- conjMaybe <$> mapM (normalizeACRest m) (funArgs fun)
            return $ (\x-> fun{funArgs=x}) <$> args
        normalizeACRest _ fom = return $ Just fom
        makeVarEmergeMap:: Fom -> M.Map String Int
        makeVarEmergeMap fom = execState (makeVarEmergeMap fom) M.empty where
            makeVarEmergeMap:: Fom -> State (M.Map String Int) ()
            makeVarEmergeMap (VarFom id _) = state $ ((), ) . M.alter (Just . maybe 1 (1+)) (idStr id)
            makeVarEmergeMap fun@FunFom{} = mapM_ makeVarEmergeMap $ funArgs fun
            makeVarEmergeMap fom = return ()
        varEmergeMap:: [Fom] -> M.Map String Int
        varEmergeMap foms = execState (mapM_ varEmergeMap foms) M.empty where
            varEmergeMap:: Fom -> State (M.Map String Int) ()
            varEmergeMap (VarFom id _) = state $ ((), ) . M.alter (Just . maybe 1 (1+)) (idStr id)
            varEmergeMap fom = return ()
        isVarWithNames:: [String] -> Fom -> Bool
        isVarWithNames names var@VarFom{} = idStr (varIdent var) `elem` names
        isVarWithNames _ _ = False
        acInsert:: [String] -> Fom -> Fom
        acInsert [] fom = fom
        acInsert (x:xs) fom = acInsert xs $ ACInsertFom x fom

    boxACRest:: (Maybe Fom, Maybe Fom) -> (Maybe Fom, Maybe Fom)
    boxACRest (Just fun@(FunFom ACFun id ty _), Just af) =
        (Just $ ACRestFom "_" fun, Just fun{funArgs=[VarFom (Ident NonePosition "_") ty, af]})
    boxACRest pair = pair
buildRule fom = analyzeErrorM (showExprIdent fom) "命題ではありません"
