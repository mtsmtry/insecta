module Analyzer.Prover where
import Analyzer.Data

buildCmd:: IdentWith Command -> Analyzer Command
buildCmd (id, cmd) = if cmd `elem` [StepCmd, ImplCmd, FoldCmd, UnfoldCmd] 
    then return cmd
    else analyzeError id "無効な命令です" >>= const (return WrongCmd)

buildStrategyRewrite:: IdentWith Statement -> Analyzer (Maybe StrategyRewrite)
buildStrategyRewrite (id, CmdStm (_, InsertCmd) exp) = do
    fom <- buildFom exp
    return $ Just $ maybe WrongRewrite InsertRewrite fom

buildStrategyRewrite (id, CmdStm idCmd exp) = do
    cmd <- buildCmd idCmd
    fom <- if cmd == UnfoldCmd
        then buildFomEx AllowUndefined exp
        else buildFom exp
    let mRew = CmdRewrite cmd <$> fom
    return $ Just $ fromMaybe WrongRewrite mRew

buildStrategyRewrite (id, AssumeStm idCmd assume stm) = do
    cmd <- buildCmd idCmd
    fom <- buildFom assume
    block <- buildStrategy stm
    let proof = AssumeRewrite cmd <$> fom <*> Just block
    return $ Just $ fromMaybe WrongRewrite proof

buildStrategyRewrite (id, ForkStm list) = do
    forks <- mapM buildFork list
    return $ Just $ ForkRewrite forks
    where
    buildFork:: [IdentWith Statement] -> Analyzer (Command, Strategy)
    buildFork stms = do
        block <- buildStrategy stms
        return (BeginCmd, block)

buildStrategyRewrite (id, VarDecStm decs) = do
    vars <- mapM buildQtfVariable decs
    mapM_ (maybeM insertVar) vars
    return Nothing

buildStrategyWithCmd:: [IdentWith Statement] -> Analyzer (Command, Strategy)
buildStrategyWithCmd all@((id, cmd):xs) = case cmd of
    (CmdStm (id, cmd) exp) -> do
        stg <- buildStrategy xs
        return (cmd, stg)

buildStrategy:: [IdentWith Statement] -> Analyzer Strategy
buildStrategy all@((id, cmd):xs) = case cmd of
    (CmdStm (id, BeginCmd) exp) -> do
        fom <- buildFom exp
        rew <- buildStrategyRewriteList xs
        let org = maybe StrategyOriginWrong StrategyOriginFom fom
        return $ Strategy (StrategyOriginIdent id org) rew
    (CmdStm (_, TargetCmd) exp) -> do
        rew <- buildStrategyRewriteList xs
        org <- case exp of
            (IdentExpr (Ident _ "left")) -> return StrategyOriginLeft
            exp -> do
                fom <- buildFom exp
                return $ maybe StrategyOriginWrong StrategyOriginContext fom
        return $ Strategy (StrategyOriginIdent id org) rew
    _ -> do
        rew <- buildStrategyRewriteList all
        return $ Strategy (StrategyOriginIdent id StrategyOriginAuto) rew
    where
    buildStrategyRewriteList xs = catMaybes <$> mapM buildStrategyRewrite xs

checkContext:: Fom -> Analyzer (Maybe [(Entity, Fom)])
checkContext con = do
    let props = extractArgs "&" con
    conjMaybe <$> mapM checkCon props
    where
    checkCon:: Fom -> Analyzer (Maybe (Entity, Fom))
    checkCon (PredFom (VarFom id _) ty) = do
        mEnt <- lookupEnt $ idStr id
        case mEnt of
            Just ent -> if entType ent == ty
                then return $ Just (ent, ty)
                else analyzeErrorM id "型が異なります"
            Nothing -> analyzeErrorM id "コンテキストにありません"
    checkCon fom = analyzeErrorM (showIdent fom) "述語ではありません"

buildProofOrigin:: StrategyOrigin -> Analyzer (ProofOrigin, Fom)
buildProofOrigin (StrategyOriginContext con) = do
    preds <- checkContext con
    return (maybe ProofOriginWrong ProofOriginContext preds, con)
buildProofOrigin (StrategyOriginFom fom) = return (ProofOriginFom fom, fom)
buildProofOrigin StrategyOriginWrong = return (ProofOriginWrong, UnknownFom)

derivateCheck:: String -> Fom -> Command -> Fom -> Maybe Fom -> Analyzer ProofCommand
derivateCheck str trg cmd goal (Just proof) = return $ ProofCommand cmd proof
derivateCheck str trg cmd goal Nothing = do
    strTrg <- onOpeMap showFom trg
    strGoal <- onOpeMap showLatestFom goal
    analyzeError (showIdent goal) $ str ++ "によって'" ++ strTrg ++ "'から'" ++ strGoal ++ "'を導出できません"
    return $ ProofCommand cmd goal

buildProofCommand:: Fom -> Command -> Fom -> Analyzer ProofCommand
buildProofCommand trg StepCmd goal = do
    sTrg <- simplify trg
    sGoal <- simplify goal
    case mergeRewrite sTrg sGoal of
        Just proof -> return $ ProofCommand StepCmd proof
        Nothing -> do
            strTrg <- onOpeMap showLatestFom sTrg
            strGoal <- onOpeMap showLatestFom sGoal
            let msg = "簡略形は'" ++ strTrg ++ "'と'" ++ strGoal ++ "'であり、一致しません"
            analyzeError (showIdent goal) msg
            return $ ProofCommand StepCmd goal
buildProofCommand trg ImplCmd   goal = derivate (trg, goal)       >>= derivateCheck "含意命題" trg ImplCmd goal
buildProofCommand trg UnfoldCmd goal = derivateUnfold (trg, goal) >>= derivateCheck "定義の展開" trg UnfoldCmd goal
buildProofCommand trg FoldCmd   goal = derivateFold (trg, goal)   >>= derivateCheck "定義の畳み込み" trg UnfoldCmd goal
buildProofCommand trg WrongCmd  goal = return $ ProofCommand WrongCmd goal

buildProofProcess:: Fom -> StrategyRewrite -> Analyzer (ProofProcess, Fom)
buildProofProcess trg (InsertRewrite fom) = do
    checkContext fom
    return (InsertProcess fom, makeBinary "&" trg fom)

buildProofProcess trg (CmdRewrite cmd goal) = do
    proc <- buildProofCommand trg cmd goal
    return (CmdProcess proc, goal)

buildProofProcess trg (AssumeRewrite cmd assume main) = do
    mainProof <- buildProof main Nothing
    let firstFom = makeBinary "=>" assume (prfBegin mainProof)
    proofCmd <- buildProofCommand trg cmd firstFom
    let lastFom = makeBinary "=>" assume (prfEnd mainProof)
    return (AssumeProcess proofCmd assume mainProof, lastFom)

buildProofProcess trg WrongRewrite = return (WrongProcess, UnknownFom)

buildProof:: Strategy -> Maybe Rule -> Analyzer Proof
buildProof (Strategy (StrategyOriginIdent idOrg stOrg) rews) mRule = do
    nOrg <- case (mRule, stOrg) of
        (Just rule, StrategyOriginAuto)  -> return $ StrategyOriginFom $ head $ funArgs $ ruleProp rule
        (Just rule, StrategyOriginLeft)  -> return $ StrategyOriginFom $ head $ funArgs $ ruleProp rule
        (Just rule, StrategyOriginWhole) -> return $ StrategyOriginFom $ ruleProp rule
        (Nothing, StrategyOriginAuto)  -> buildError "証明の対象が宣言されていません"
        (Nothing, StrategyOriginLeft)  -> buildError "ルートスコープ以外では使用できません"
        (Nothing, StrategyOriginWhole) -> buildError "ルートスコープ以外では使用できません"
        (_, org) -> return org
    (org, begin) <- buildProofOrigin nOrg
    (list, end) <- buildProofProcessList begin rews
    case mRule of
        Just rule -> do
            let trg = case stOrg of 
                    StrategyOriginWhole -> VarFom (Ident NonePosition "True") TypeOfType
                    _ -> last $ funArgs $ ruleProp rule
            strTrg <- onOpeMap showLatestFom end
            strGoal <- onOpeMap showLatestFom trg
            let msg = "最後の命題が'" ++ strTrg ++ "'であるのに対し、目標の命題は'" ++ strGoal ++ "'あり、一致しません"
            when (end /= trg) $ analyzeError (showIdent end) msg
        Nothing -> return ()
    return $ Proof org list begin end
    where
    buildError:: String -> Analyzer StrategyOrigin
    buildError str = analyzeError idOrg str >>= const (return StrategyOriginWrong)
    buildProofProcessList:: Fom -> [StrategyRewrite] -> Analyzer ([ProofProcess], Fom)
    buildProofProcessList trg [] = return ([], trg)
    buildProofProcessList trg (x:xs) = do
        (proc, goal) <- buildProofProcess trg x
        (rest, end) <- buildProofProcessList goal xs
        return (proc:rest, end)