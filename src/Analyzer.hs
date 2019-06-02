module Analyzer where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import qualified Data.Foldable as F
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
import Visualizer

onRule:: (Fom -> Fom -> Bool) -> Rule -> Bool
onRule f rule = f (ruleBf rule) (ruleAf rule)

isCommutativeRule:: Rule -> Bool
isCommutativeRule = onRule isCommutative where
    isCommutative:: Fom -> Fom -> Bool
    isCommutative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
        ([a, b], [c, d]) -> funName bf == funName af && a == d && b == c
        _ -> False
    isCommutative _ _ = False

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
        sameName (x:xs) = let name = funName x in all (\t-> name == funName t) xs
    isAssociative _ _ = False

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
        AFun -> nAssoc
        ACFun{} -> nAssoc
        _ -> fun{funArgs=map normalizeAC args}
        where
        nAssoc = if length args == length nArgs then fun else nFun
        args = funArgs fun
        nArgs = concatMap (extractArgs (idStr $ funName fun)) args
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
        maybeFlip mEnt (analyzeErrorM id "宣言されていない識別子です") $ \ent-> do
            let ty = entType ent
            nArgs <- checkFunc ty mArgs
            return $ case ty of
                tyFun@FunTypeFom{} -> FunFom (entFunAttr ent) id (funRetType tyFun) <$> conjMaybe nArgs
                _ -> Nothing
        where
        checkFunc:: Fom -> [Maybe Fom] -> Analyzer [Maybe Fom]
        checkFunc (FunTypeFom _ argTys retTy) argVls = if length argTys /= length argVls
                then do
                    analyzeErrorB id "引数の数が異なります"
                    return argVls
                else zipWithM checkType argVls argTys
        checkFunc _ vls = do
            analyzeErrorB id $ "Not function:" ++ idStr id
            return vls
        checkType:: Maybe Fom -> Fom -> Analyzer (Maybe Fom)
        checkType (Just (VarFom id UnknownFom)) ty = return $ Just $ VarFom id ty
        checkType trg@(Just vl) ty = let vlTy = evalType vl in if vlTy == ty || vlTy == UnknownFom 
            then return trg
            else do
                vStr <- onOpeMap showFom vl
                eStr <- onOpeMap showFom vlTy
                aStr <- onOpeMap showFom ty
                let msg = "'" ++ vStr ++ "'は'" ++ aStr ++ "'型である必要がありますが、実際は'" ++ eStr ++ "'型です"
                analyzeError (showIdent vl) msg
                return trg
        checkType _ _ = return Nothing

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
        "=>"  -> normalizeACRule (bfFom, afFom) >>= checkType ImplRule "Prop"
        "<=>" -> checkType EqualRule "Prop" (bfFom, afFom)
        ">>=" -> normalizeACRule (bfFom, afFom) >>= sameType SimpRule
        "="   -> normalizeACRule (bfFom, afFom) >>= sameType EqualRule
        _     -> analyzeErrorM rId "無効な命題です"
    where
    checkType:: RuleKind -> String -> (Maybe Fom, Maybe Fom) -> Analyzer (Maybe Rule)
    checkType kind ty (bf, af) = do
        chBf <- checkType bf
        chAf <- checkType af
        label <- maybe (return Nothing) getLabel chBf
        return $ Rule kind rId Nothing <$> label <*> chBf <*> chAf
        where
        checkType (Just fom) = if evalType fom == makeType ty 
            then return $ Just fom
            else analyzeErrorM (funName fom) "命題ではありません"
        checkType Nothing = return Nothing
    getLabel:: Fom -> Analyzer (Maybe String)
    getLabel (ACRestFom _ fun) = getLabel fun
    getLabel fun@FunFom{} = return $ Just $ idStr $ funName fun
    getLabel fom = analyzeErrorM (showIdent fom) "左辺は関数値である必要があります"
    sameType:: RuleKind -> (Maybe Fom, Maybe Fom) -> Analyzer (Maybe Rule)
    sameType kind (Just bf, Just af) = if evalType bf == evalType af
        then do
            label <- getLabel bf
            return $ Rule kind rId Nothing <$> label <*> Just bf <*> Just af
        else analyzeErrorM rId "両辺の型が一致しません"
    sameType _ _ = return Nothing

    normalizeACRule:: (Maybe Fom, Maybe Fom) -> Analyzer (Maybe Fom, Maybe Fom)
    normalizeACRule (a, b) = do 
        a' <- maybe (return Nothing) normalizeACRest a
        -- b' <- maybe (return Nothing) normalizeACRest b
        return $ boxACRest (a', b)
    normalizeACRest:: Fom -> Analyzer (Maybe Fom)
    normalizeACRest fun@(FunFom ACFun _ _ _) = do
        let oneEmergeVars = map fst $ filter ((==1) . snd) $ M.toList $ varEmergeMap $ funArgs fun
        args <- conjMaybe <$> mapM normalizeACRest (funArgs fun)
        case oneEmergeVars of
            [] -> return $ (\x-> fun{funArgs=x}) <$> args
            var:_ -> return $ (\x-> ACRestFom var fun{funArgs=filter (not . isVarWithName var) x}) <$> args
            -- _ -> analyzeErrorM (funName fun) $ show oneEmergeVars ++ ":AC演算子の余剰項の代入候補となる変数が2つ以上あり、代入方法が決定不能です"
        where
        isVarWithName:: String -> Fom -> Bool
        isVarWithName name var@VarFom{} = name == idStr (varName var)
        isVarWithName _ _ = False
        varEmergeMap:: [Fom] -> M.Map String Int
        varEmergeMap foms = execState (mapM_ varEmergeMap foms) M.empty where
            varEmergeMap:: Fom -> State (M.Map String Int) ()
            varEmergeMap (VarFom id _) = state $ ((), ) . M.alter (Just . maybe 1 (1+)) (idStr id)
            varEmergeMap fom = return ()
    normalizeACRest fom = return $ Just fom
    boxACRest:: (Maybe Fom, Maybe Fom) -> (Maybe Fom, Maybe Fom)
    boxACRest (Just fun@(FunFom ACFun id ty _), Just af) =
        (Just $ ACRestFom "_" fun, Just fun{funArgs=[VarFom (Ident NonePosition "_") ty, af]})
    boxACRest pair = pair

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
        enableAssoc = \case attr@ACFun{}-> attr; CFun-> ACFun; OFun-> AFun; AFun-> AFun
        enableCommu = \case attr@ACFun{}-> attr; CFun-> CFun; OFun-> CFun; AFun-> ACFun

buildCmd:: IdentWith Command -> Analyzer Command
buildCmd (id, StepCmd) = return StepCmd
buildCmd (id, ImplCmd) = return ImplCmd
buildCmd (id, UnfoldCmd) = return UnfoldCmd
buildCmd (id, _) = do
    analyzeErrorM id "無効な命令です"
    return WrongCmd

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

derivateError:: String -> Fom -> Command -> Fom -> Analyzer ProofCommand
derivateError str trg cmd goal = do
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

buildProofCommand trg ImplCmd goal = do
    res <- derivate (trg, goal)
    case res of
        Just proof -> return $ ProofCommand ImplCmd proof
        Nothing -> derivateError "含意命題" trg ImplCmd goal

buildProofCommand trg UnfoldCmd goal = do
    res <- derivateUnfold (trg, goal)
    case res of
        Just proof -> return $ ProofCommand UnfoldCmd proof
        Nothing -> derivateError "定義の展開" trg UnfoldCmd goal

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
        (Just rule, StrategyOriginAuto) -> return $ StrategyOriginFom $ ruleBf rule
        (Just rule, StrategyOriginLeft) -> return $ StrategyOriginFom $ ruleBf rule
        (Just rule, StrategyOriginWhole) -> case ruleKind rule of
            SimpRule -> return $ StrategyOriginFom $ makeBinary "=" (ruleBf rule) (ruleAf rule)
            ImplRule -> return $ StrategyOriginFom $ makeBinary "=>" (ruleBf rule) (ruleAf rule)
        (Nothing, StrategyOriginLeft) -> buildError "ルートスコープ以外では使用できません"
        (Nothing, StrategyOriginWhole) -> buildError "ルートスコープ以外では使用できません"
        (Nothing, StrategyOriginAuto) -> buildError "証明の対象が宣言されていません"
        (_, org) -> return org
    (org, begin) <- buildProofOrigin nOrg
    (list, end) <- buildProofProcessList begin rews
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

loadVarDec:: (Ident, Expr) -> Analyzer ()
loadVarDec (id, exp) = do
    mFom <- buildFom exp
    maybe (return ()) (insertEnt id) mFom

loadVarDecs:: [[(Ident, Expr)]] -> Analyzer ()
loadVarDecs = mapM_ (mapM_ loadVarDec)

loadDecla:: Decla -> Analyzer ()
loadDecla (TheoremDecla decs prop stms) = do
    (prf, mRule) <- subScope $ do
        loadVarDecs decs
        mRule <- buildRule prop
        prf <- maybe (return Nothing) (\rule-> Just <$> loadProof rule stms) mRule
        return (prf, mRule)
    maybe (return ()) (\rule-> insertRule rule{ruleProof=prf}) mRule

loadDecla (AxiomDecla decs prop) = do
    mRule <- subScope $ do
        loadVarDecs decs
        buildRule prop
    maybe (return ()) insertRule mRule

loadDecla (UndefDecla id ty mTex) = do
    mTy <- subScope $ buildFom ty
    maybe (return ()) (\ty-> insertEntMap id ty $ \ent-> ent{entLatex=mTex}) mTy
    
loadDecla (DefineDecla id decs ret def) = do
    (mArgTys, mRetTy, mDef, scope) <- subScope $ do
        loadVarDecs decs
        mArgTys <- mapM (buildFom . snd) (last decs)
        mRetTy <- buildFom ret
        mDef <- buildFom def
        scope <- getLocalEntMap
        return (mArgTys, mRetTy, mDef, scope)
    case (conjMaybe mArgTys, mRetTy, mDef) of
        (Just argTys, Just retTy, Just body) -> do
            let def = Define { defScope=scope, defBody=body, defArgs=map (idStr . fst) $ last decs} 
            let ty = FunTypeFom { funTypeIdent = id, funArgTypes = argTys, funRetType = retTy }
            insertEntMap id ty $ \ent-> ent{entDef=Just def}
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