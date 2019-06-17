module Analyzer.Declaration where
import Analyzer.Data

onRule:: (Fom -> Fom -> a) -> Rule -> a
onRule f rule = f (ruleBf rule) (ruleAf rule)

-- f(a, b) = f(b, a)
isCommutativeRule:: Rule -> Bool
isCommutativeRule = onRule isCommutative where
    isCommutative:: Fom -> Fom -> Bool
    isCommutative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
        ([a, b], [c, d]) -> funIdent bf == funIdent af && a == d && b == c
        _ -> False
    isCommutative _ _ = False

-- f(a, f(b, c)) = f(f(a, b), c)
isAssociativeRule:: Rule -> Bool
isAssociativeRule = onRule isAssociative where
    isAssociative:: Fom -> Fom -> Bool
    isAssociative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
        ([f@FunFom{}, c], [x, g@FunFom{}]) -> case (funArgs f, funArgs g) of
            ([a, b], [y, z]) -> sameName [bf, af, f, g] && all (uncurry (==)) [(a, x), (b, y), (c, z)]
            _ -> False
        ([a, f@FunFom{}], [g@FunFom{}, z]) -> case (funArgs f, funArgs g) of
            ([b, c], [x, y]) -> sameName [bf, af, f, g] && all (uncurry (==)) [(a, x), (b, y), (c, z)]
            _ -> False
        _ -> False
        where
        sameName:: [Fom] -> Bool
        sameName (x:xs) = let name = funIdent x in all (\t-> name == funIdent t) xs
    isAssociative _ _ = False

-- f(g(a, b)) = h(f(a), f(b))
isDistributive:: Fom -> Fom -> Maybe (Fom, Fom, UnaryLambda)
isDistributive bf afFun@(FunFom ACFun id _ [lf, rg]) = case diffVarList lf rg of
    Just [(a, b)] -> case unifyUnaryLambda lambda bf of
        Just bfFun@(FunFom ACFun _ _ args) -> if args == [a, b] then Just (bfFun, afFun, lambda) else Nothing
        _ -> Nothing
        where
        lambda = UnaryLambda (idStr $ varIdent a) lf
    Nothing -> Nothing
    where
    diffVarList:: Fom -> Fom -> Maybe [(Fom, Fom)]
    diffVarList lf@VarFom{} rg@VarFom{} = if lf == rg then Just [] else Just [(lf, rg)]
    diffVarList lf@FunFom{} rg@FunFom{} = if funIdent lf == funIdent rg
        then concat <$> conjMaybe (zipWith diffVarList (funArgs lf) (funArgs rg))
        else Nothing
    diffVarList lf rg = if lf == rg then Just [] else Nothing
    unifyUnaryLambda:: UnaryLambda -> Fom -> Maybe Fom
    unifyUnaryLambda (UnaryLambda arg ptn) trg = unify ptn trg >>= M.lookup arg
isDistributive _ _ = Nothing

isACInsert:: Fom -> Fom -> Maybe (Fom, Fom)
isACInsert bf@(FunFom ACFun id _ [x@VarFom{}, y@VarFom{}]) af@VarFom{} = if y == af
    then Just (ACRestFom (idStr $ varIdent x) (ACInsertFom (idStr $ varIdent y) bf{funArgs=[]}), y)
    else Nothing
isACInsert _ _ = Nothing

data BuildFomOption = AllowUndefined | NotAllowUndefined deriving(Eq, Show)


buildVariable:: VarDec -> Analyzer (Maybe Variable)
buildVariable (VarDec kind id exp) = do
    mFom' <- buildFom exp
    let mFom = if kind == NormalTyping then mFom' else SubTypeFom <$> mFom'
    return $ Variable id <$> mFom

buildQtfVariable:: QtfVarDec -> Analyzer (Maybe QtfVariable)
buildQtfVariable (QtfVarDec qtf dec) = do
    var <- buildVariable dec
    maybeN (return . Just . (QtfVariable qtf)) var

makeVarEmergeMap:: Fom -> M.Map String Int
makeVarEmergeMap fom = execState (makeVarEmergeMap fom) M.empty where
    makeVarEmergeMap:: Fom -> State (M.Map String Int) ()
    makeVarEmergeMap (VarFom id _) = state $ ((), ) . M.alter (Just . maybe 1 (1+)) (idStr id)
    makeVarEmergeMap fun@FunFom{} = mapM_ makeVarEmergeMap $ funArgs fun
    makeVarEmergeMap fom = return ()
forkList:: (a -> Bool) -> [a] -> ([a], [a]) -> ([a], [a])
forkList f (x:xs) (as, bs) = if f x then (x:as, bs) else (as, x:bs)

returnMessage:: a -> Message -> Analyzer a
returnMessage a m = Analyzer ([m], , a)

insertRule:: Rule -> Analyzer ()
insertRule rule = case ruleKind rule of
    SimpRule -> do
        insertSimp (ruleIdent rule) (ruleBf rule) (ruleAf rule)
        updateSimp $ insertRuleToMap rule
    ImplRule -> updateImpl $ insertRuleToMap rule
    EqualRule
        | isAssociativeRule rule -> updateFunAttr (ruleLabel rule) enableAssoc
        | isCommutativeRule rule -> updateFunAttr (ruleLabel rule) enableCommu
        | otherwise -> analyzeError (ruleIdent rule) "交換律でも結合律でもありません"
        where
        enableAssoc = \case ACFun-> ACFun; CFun-> ACFun; OFun-> AFun; AFun-> AFun
        enableCommu = \case ACFun-> ACFun; CFun-> CFun; OFun-> CFun; AFun-> ACFun

insertVar:: QtfVariable -> Analyzer ()
insertVar (QtfVariable qtf (Variable id ty)) = insertEntMap id ty $ \ent-> ent{entQtf=qtf}


loadProof:: Rule -> [IdentWith Statement] -> Analyzer Proof
loadProof rule stms = do
    stg <- buildStrategy stms
    buildProof stg $ Just rule

loadVariables:: [[VarDec]] -> Analyzer (Maybe [Variable])
loadVariables varDecs = do
    vars <- mapM loadVarDecs varDecs
    return $ last vars

loadVarDecs:: [VarDec] -> Analyzer (Maybe [Variable])
loadVarDecs varDec = do
    vars <- mapM buildVariable varDec
    mapM_ (maybeM (\(Variable id ty)-> insertEnt id ty)) vars
    return $ conjMaybe vars

loadStatement:: IdentWith Statement -> Analyzer ()
loadStatement (id, VarDecStm decs) = do
    vars <- mapM buildQtfVariable decs
    mapM_ (maybeM insertVar) vars
loadStatement (id, _) = analyzeError id "このステートメントは使用できません"

loadDeclaBody:: DeclaBody -> Analyzer (Maybe Fom)
loadDeclaBody (DeclaBody stms def) = mapM_ loadStatement stms >>= const (buildFom def)
loadDeclaRule:: DeclaBody -> Analyzer (Maybe Rule)
loadDeclaRule (DeclaBody stms def) = mapM_ loadStatement stms >>= const (buildRule def)

loadDecla:: Decla -> Analyzer ()
loadDecla (TheoremDecla decs prop stms) = do
    (prf, rule) <- subScope $ do
        loadVariables decs
        rule <- loadDeclaRule prop
        prf  <- maybe (return Nothing) (\rule-> Just <$> loadProof rule stms) rule
        return (prf, rule)
    maybeM (\rule-> insertRule rule{ruleProof=prf}) rule

loadDecla (AxiomDecla decs prop) = do
    mRule <- subScope $ do
        loadVariables decs
        loadDeclaRule prop
    maybeM insertRule mRule

loadDecla (UndefDecla id ty mTex) = do
    mTy <- subScope $ buildFom ty
    maybeM (\ty-> insertEntMap id ty $ \ent-> ent{entLatex=mTex}) mTy

loadDecla (DefineDecla id decs ret def) = do
    tuple <- subScope $ do
        args  <- loadVariables decs
        retTy <- buildFom ret
        body  <- loadDeclaBody def
        scope <- getLocalEntMap
        return (args, retTy, body, scope)
    case tuple of
        (Just args, Just retTy, Just body, scope) -> do
            let def = Define { defScope=scope, defBody=body, defArgs=args } 
            let ty = FunTypeFom { funTypeIdent=id, funArgTypes=map varTy args, funRetType=retTy }
            insertEntMap id ty $ \ent-> ent{entDef=Just def}
        _ -> return ()

loadDecla (PredicateDecla id decs this thisTy def) = do
    tuple <- subScope $ do
        args   <- loadVariables decs
        thisTy <- buildFom thisTy
        maybeM (insertEnt this) thisTy
        body   <- loadDeclaBody def
        scope  <- getLocalEntMap
        return (args, thisTy, body, scope)
    case tuple of
        (Just args, Just thisTy, Just body, scope) -> do
            let def = Define { defScope=scope, defBody=body, defArgs=args } 
            insertEntMap id TypeOfType $ \ent-> ent{ entPred=Just (Variable this thisTy), entDef=Just def }
        _ -> return ()

loadDecla (DataTypeDecla id def) = do
    insertEnt id TypeOfType
    mapM_ insertCstr $ extractArgs "|" def
    where
    tyFom = makeType (idStr id)
    insertCstr:: Expr -> Analyzer ()
    insertCstr (IdentExpr id) = insertEnt id tyFom
    insertCstr (FunExpr id args) = do
        mArgs <- mapM buildFom args
        mapM_ checkType mArgs
        (flip $ maybe $ return ()) (conjMaybe mArgs) $ \args-> do
            let ty = FunTypeFom { funTypeIdent=id, funArgTypes=args, funRetType=tyFom }
            insertEnt id ty
        where
        checkType:: Maybe Fom -> Analyzer ()
        checkType (Just fom) = when (evalType fom /= TypeOfType) (analyzeError id "型ではありません")
        checkType Nothing = return ()
    insertCstr e = error $ show e
    extractArgs:: String -> Expr -> [Expr]
    extractArgs str fun@(FunExpr id args) = if str == idStr id then concatMap (extractArgs str) args else [fun]
    extractArgs str expr = [expr]    

loadDecla _ = return ()

buildProgram:: String -> ([Message], Context)
buildProgram prg = (msg ++ msg', ctx)  where
    (msg, declas, omap) = parseProgram prg
    (msg', ctx, _) = analyze (mapM_ loadDecla declas) (newContext omap)