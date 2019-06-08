module Analyzer where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Set as S
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

buildFom:: Expr -> Analyzer (Maybe Fom)
buildFom = buildFomEx NotAllowUndefined

buildFomEx:: BuildFomOption -> Expr -> Analyzer (Maybe Fom)
buildFomEx opt exp = do
    fom <- buildFom exp
    return $ normalizeAC <$> fom
    where
    normalizeAC:: Fom -> Fom
    normalizeAC fun@(FunFom ACFun _ _ [x]) = normalizeAC x
    normalizeAC fun@(FunFom AFun _ _ [x]) = normalizeAC x
    normalizeAC fun@FunFom{} = case funAttr fun of
        AFun -> nFun
        ACFun -> nFun
        _ -> fun{funArgs=map normalizeAC args}
        where
        args = funArgs fun
        nArgs = concatMap (extractArgs (idStr $ funIdent fun)) args
        nFun = fun{funArgs=map (normalizeAC . latestFom) nArgs}
    normalizeAC fom = fom
    buildFom:: Expr -> Analyzer (Maybe Fom)
    buildFom (NumExpr num) = return $ Just $ NumFom num
    buildFom (StrExpr str) = return $ Just $ StrFom str

    buildFom (IdentExpr id) = do
        mEnt <- lookupEntWithArea $ idStr id
        case mEnt of
            Just (ent, area) -> case area of
                Global -> return $ Just $ CstFom id (entType ent)
                Local -> return $ Just $ VarFom id (entType ent)
            Nothing -> if opt == AllowUndefined
                then return $ Just $ VarFom id UnknownFom
                else analyzeErrorM id "宣言されていない識別子です"

    buildFom (FunExpr id@(Ident pos "->") [arg, ret]) = do
        mArgs <- mapM buildFom (extractFromTuple arg)
        mRet <- buildFom ret
        return $ FunTypeFom id <$> conjMaybe mArgs <*> mRet
        where
        extractFromTuple:: Expr -> [Expr]
        extractFromTuple (FunExpr (Ident _ "tuple") args) = args
        extractFromTuple fom = [fom]

    buildFom e@(FunExpr id@(Ident pos fun) args) = do
        mEnt <- lookupEnt fun
        mArgs <- mapM buildFom args
        (flip $ maybe $ analyzeErrorM id "宣言されていない識別子です") mEnt $ \ent->
            case (entPred ent, entDef ent) of
                (Just this, Just def) -> analyzePred this def (entType ent) mArgs
                _ -> analyzeFun (entFunAttr ent) (entType ent) mArgs
        where
        analyzeFun:: FunAttr -> Fom -> [Maybe Fom] -> Analyzer (Maybe Fom)
        analyzeFun attr ty mArgs = do
            nArgs <- case ty of 
                (FunTypeFom _ argTys retTy) -> conjMaybe <$> checkArgs argTys mArgs
                _ -> analyzeErrorM id $ "'" ++ idStr id ++ "'は関数ではありません"
            return $ case ty of
                tyFun@FunTypeFom{} -> FunFom attr id (funRetType tyFun) <$> nArgs
                _ -> Nothing
        analyzePred:: Variable -> Define -> Fom -> [Maybe Fom] -> Analyzer (Maybe Fom)
        analyzePred this def ty mArgs = do
            args <- checkArgs (map varTy $ defArgs def) mArgs
            return $ (Just $ PredTypeFom id) <*> conjMaybe args
        checkArgs:: [Fom] -> [Maybe Fom] -> Analyzer [Maybe Fom]
        checkArgs argTys argVls = if length argTys /= length argVls
            then do
                analyzeErrorB id "引数の数が異なります"
                return argVls
            else zipWithM checkType argVls argTys
        checkType:: Maybe Fom -> Fom -> Analyzer (Maybe Fom)
        checkType (Just (VarFom id UnknownFom)) ty = return $ Just $ VarFom id ty
        checkType trg@(Just vl) ty = let vlTy = evalType vl in if checkType ty vlTy || vlTy == UnknownFom 
            then return trg
            else do
                vStr <- onOpeMap showFom vl
                eStr <- onOpeMap showFom vlTy
                aStr <- onOpeMap showFom ty
                let msg = "'" ++ vStr ++ "'は'" ++ aStr ++ "'型である必要がありますが、実際は'" ++ eStr ++ "'型です"
                analyzeError (showIdent vl) msg
                return trg
            where
            checkType:: Fom -> Fom -> Bool
            checkType expect actual = expect == actual || case evalType actual of
                SubTypeFom sub -> checkType expect sub
                _ -> False
        checkType _ _ = return Nothing

buildVariable:: VarDec -> Analyzer (Maybe Variable)
buildVariable (VarDec kind id exp) = do
    mFom' <- buildFom exp
    let mFom = if kind == NormalTyping then mFom' else SubTypeFom <$> mFom'
    return $ Variable id <$> mFom

makeVarEmergeMap:: Fom -> M.Map String Int
makeVarEmergeMap fom = execState (makeVarEmergeMap fom) M.empty where
    makeVarEmergeMap:: Fom -> State (M.Map String Int) ()
    makeVarEmergeMap (VarFom id _) = state $ ((), ) . M.alter (Just . maybe 1 (1+)) (idStr id)
    makeVarEmergeMap fun@FunFom{} = mapM_ makeVarEmergeMap $ funArgs fun
    makeVarEmergeMap fom = return ()
forkList:: (a -> Bool) -> [a] -> ([a], [a]) -> ([a], [a])
forkList f (x:xs) (as, bs) = if f x then (x:as, bs) else (as, x:bs)

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

buildCmd:: IdentWith Command -> Analyzer Command
buildCmd (id, cmd) = if cmd `elem` [StepCmd, ImplCmd, FoldCmd, UnfoldCmd] 
    then return cmd
    else analyzeError id "無効な命令です" >>= const (return WrongCmd)

buildStrategyRewrite:: IdentWith Statement -> Analyzer (Maybe StrategyRewrite)
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
    buildFork:: (IdentWith Command, [IdentWith Statement]) -> Analyzer (Command, Strategy)
    buildFork (idCmd, stms) = do
        cmd <- buildCmd idCmd
        block <- buildStrategy stms
        return (cmd, block)

buildStrategyRewrite (id, ForAllStm var ty) = do
    mFom <- buildFom ty
    F.forM_ mFom (insertEnt var)
    return Nothing

buildStrategyRewrite (id, ExistsStm var refs ty) = do
    mFom <- buildFom ty
    case mFom of
        Just fom -> insertEntMap var fom $ \ent-> ent{entQtf=Exists refs}
        Nothing -> return ()
    return Nothing

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

buildProofOrigin:: StrategyOrigin -> Analyzer (ProofOrigin, Fom)
buildProofOrigin (StrategyOriginContext con) = do
    let props = extractArgs "&" con
    preds <- conjMaybe <$> mapM checkCon props
    return (maybe ProofOriginWrong ProofOriginContext preds, con)
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
buildProofCommand trg ImplCmd goal = derivate (trg, goal) >>= derivateCheck "含意命題" trg ImplCmd goal
buildProofCommand trg UnfoldCmd goal = derivateUnfold (trg, goal) >>= derivateCheck "定義の展開" trg UnfoldCmd goal
buildProofCommand trg FoldCmd goal = derivateFold (trg, goal) >>= derivateCheck "定義の畳み込み" trg UnfoldCmd goal
buildProofCommand trg WrongCmd goal = return $ ProofCommand WrongCmd goal

buildProofProcess:: Fom -> StrategyRewrite -> Analyzer (ProofProcess, Fom)
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

loadProof:: Rule -> [IdentWith Statement] -> Analyzer Proof
loadProof rule stms = do
    stg <- buildStrategy stms
    buildProof stg $ Just rule

loadVariables:: [[VarDec]] -> Analyzer (Maybe [Variable])
loadVariables varDecs = do
    vars <- mapM loadVarDecSet varDecs
    return $ last vars
    where
    loadVarDecSet:: [VarDec] -> Analyzer (Maybe [Variable])
    loadVarDecSet varDec = do
        vars <- mapM buildVariable varDec
        mapM_ (maybeM (\(Variable id ty)-> insertEnt id ty)) vars
        return $ conjMaybe vars

loadStatement:: IdentWith Statement -> Analyzer ()
loadStatement (id, ForAllStm var ty) = do
    mFom <- buildFom ty
    maybeM (insertEnt var) mFom
loadStatement (id, ExistsStm var refs ty) = do
    mFom <- buildFom ty
    maybeM (\x-> insertEntMap var x $ \ent-> ent{entQtf=Exists refs}) mFom
loadStatement (id, _) = analyzeError id "このステートメントは使用できません"

loadDefineBody:: DefineBody -> Analyzer (Maybe Fom)
loadDefineBody (DefineBody stms def) = do
    mapM_ loadStatement stms
    buildFom def

loadDecla:: Decla -> Analyzer ()
loadDecla (TheoremDecla decs prop stms) = do
    (prf, rule) <- subScope $ do
        loadVariables decs
        rule <- buildRule prop
        prf  <- maybe (return Nothing) (\rule-> Just <$> loadProof rule stms) rule
        return (prf, rule)
    maybeM (\rule-> insertRule rule{ruleProof=prf}) rule

loadDecla (AxiomDecla decs prop) = do
    mRule <- subScope $ do
        loadVariables decs
        buildRule prop
    maybeM insertRule mRule

loadDecla (UndefDecla id ty mTex) = do
    mTy <- subScope $ buildFom ty
    maybeM (\ty-> insertEntMap id ty $ \ent-> ent{entLatex=mTex}) mTy

loadDecla (DefineDecla id decs ret def) = do
    tuple <- subScope $ do
        args  <- loadVariables decs
        retTy <- buildFom ret
        body  <- loadDefineBody def
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
        body   <- loadDefineBody def
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