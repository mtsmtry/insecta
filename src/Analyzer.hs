module Analyzer where
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
import Parser
import Rewriter
import Data
import Visualizer

onRule:: (Fom -> Fom -> Bool) -> Rule -> Bool
onRule f rule = f (ruleBf rule) (ruleAf rule)

isAssociativeRule:: Rule -> Bool
isAssociativeRule = onRule isAssociative where
    isAssociative:: Fom -> Fom -> Bool
    isAssociative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
        ([a, b], [c, d]) -> funName bf == funName af && a == d && b == c
        _ -> False
    isAssociative _ _ = False

isCommutativeRule:: Rule -> Bool
isCommutativeRule = onRule isCommutative where
    isCommutative:: Fom -> Fom -> Bool
    isCommutative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
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
    isCommutative _ _ = False

data BuildFomOption = AllowUndefined | NotAllowUndefined deriving(Eq, Show)

buildFom:: Expr -> Analyzer (Maybe Fom)
buildFom = buildFomEx NotAllowUndefined

buildFomEx:: BuildFomOption -> Expr -> Analyzer (Maybe Fom)
buildFomEx opt = buildFom where
    buildFom:: Expr -> Analyzer (Maybe Fom)
    buildFom (NumExpr num) = return $ Just $ NumFom num
    buildFom (StrExpr str) = return $ Just $ StrFom str

    buildFom (IdentExpr id) = do
        mEnt <- lookupEnt $ idStr id
        case mEnt of
            Just ent -> if entConst ent
                then return $ Just $ CstFom id (entType ent)
                else return $ Just $ VarFom id (entType ent)
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
                let msg = "'" ++ vStr ++ "'は" ++ eStr ++ "'型であると予期しましたが、実際は '" ++ aStr ++ "'型でした"
                analyzeError (showIdent vl) msg
                return trg
        checkType _ _ = return Nothing

getLabel:: Maybe Fom -> Maybe String
getLabel (Just fun@FunFom{}) = Just $ idStr $ funName fun
getLabel Nothing = Nothing

buildRule:: Expr -> Analyzer (Maybe Rule)
buildRule (FunExpr id@(Ident _ "=>") [bf, af]) = do
    let checkType (Just fom) = unless (evalType fom == makeType "Prop") (analyzeError (funName fom) "命題ではありません")
        checkType Nothing = return ()
    bfFom <- buildFom bf
    afFom <- buildFom af
    checkType bfFom
    checkType afFom
    return $ Rule ImplRule id Nothing <$> getLabel bfFom <*> bfFom <*> afFom

buildRule (FunExpr id@(Ident _ ">>=") [bf, af]) = makeEqualRule SimpRule id bf af
buildRule (FunExpr id@(Ident _ "<=>") [bf, af]) = makeEqualRule EqualRule id bf af
buildRule (FunExpr id@(Ident _ "=") [bf, af]) = makeEqualRule EqualRule id bf af

buildRule exp = analyzeErrorM (showExprIdent exp) "無効なルールです"

makeEqualRule kind id bf af = do
    let checkType (Just bf) (Just af) = evalType bf == evalType af
        checkType _ _ = False
    bfFom <- buildFom bf
    afFom' <- buildFom af
    let sameFun name (FunFom (ACFun _) (Ident _ name') _ _) = name == name'
        sameFun _ _ = False
    let afFom = case (bfFom, afFom') of
            (Just fun@(FunFom (ACFun _) (Ident _ name) _ _), Just fom) -> if sameFun name fom then afFom' else Just fun{funArgs=[fom]}
            _ -> afFom'
    if checkType bfFom afFom
        then return $ Rule kind id Nothing <$> getLabel bfFom <*> bfFom <*> afFom
        else analyzeErrorM id "両辺の型が一致しません"

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
        enableAssoc:: FunAttr -> FunAttr
        enableAssoc attr@ACFun{} = attr
        enableAssoc CFun = ACFun "_"
        enableAssoc OFun = AFun
        enableAssoc AFun = AFun
        enableCommu:: FunAttr -> FunAttr
        enableCommu attr@ACFun{} = attr
        enableCommu CFun = CFun
        enableCommu OFun = CFun
        enableCommu AFun = ACFun "_"

buildCmd:: IdentCmd -> Analyzer Command
buildCmd (IdentCmd id StepCmd) = return StepCmd
buildCmd (IdentCmd id ImplCmd) = return ImplCmd
buildCmd (IdentCmd id UnfoldCmd) = return UnfoldCmd
buildCmd (IdentCmd id _) = do
    analyzeErrorM id "無効な命令です"
    return WrongCmd

buildStrategyRewrite:: IdentStm -> Analyzer (Maybe StrategyRewrite)
buildStrategyRewrite (IdentStm id (CmdStm idCmd exp)) = do
    cmd <- buildCmd idCmd
    fom <- if cmd == UnfoldCmd
        then buildFomEx AllowUndefined exp
        else buildFom exp
    let mRew = CmdRewrite cmd <$> fom
    return $ Just $ fromMaybe WrongRewrite mRew

buildStrategyRewrite (IdentStm id (AssumeStm idCmd assume stm)) = do
    cmd <- buildCmd idCmd
    fom <- buildFom assume
    block <- buildStrategy stm
    let proof = AssumeRewrite cmd <$> fom <*> Just block
    return $ Just $ fromMaybe WrongRewrite proof

buildStrategyRewrite (IdentStm id (ForkStm list)) = do
    forks <- mapM buildFork list
    return $ Just $ ForkRewrite forks
    where
    buildFork:: (IdentCmd, [IdentStm]) -> Analyzer (Command, Strategy)
    buildFork (idCmd, stms) = do
        cmd <- buildCmd idCmd
        block <- buildStrategy stms
        return (cmd, block)

buildStrategyRewrite (IdentStm id (ForAllStm var ty)) = do
    mFom <- buildFom ty
    case mFom of
        Just fom -> updateVar $ M.insert (idStr var) $ Variable ForAll fom
        Nothing -> return ()
    return Nothing

buildStrategyRewrite (IdentStm id (ExistsStm var refs ty)) = do
    mFom <- buildFom ty
    case mFom of
        Just fom -> updateVar $ M.insert (idStr var) $ Variable (Exists refs) fom
        Nothing -> return ()
    return Nothing

buildStrategy:: [IdentStm] -> Analyzer Strategy
buildStrategy all@(IdentStm id cmd:xs) = case cmd of
    (CmdStm (IdentCmd id BeginCmd) exp) -> do
        fom <- buildFom exp
        rew <- buildStrategyRewriteList xs
        let org = maybe StrategyOriginWrong StrategyOriginFom fom
        return $ Strategy (StrategyOriginIdent id org) rew
    (CmdStm (IdentCmd _ TargetCmd) exp) -> do
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
    buildStrategyRewriteList xs = extractMaybe <$> mapM buildStrategyRewrite xs

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
        Nothing -> do
            strTrg <- onOpeMap showFom trg
            strGoal <- onOpeMap showLatestFom goal
            analyzeError (showIdent goal) $ "'" ++ strTrg ++ "'から'" ++ strGoal ++ "'を導出できません"
            return $ ProofCommand ImplCmd goal

buildProofCommand trg UnfoldCmd goal = do
    res <- derivateUnfold (trg, goal)
    case res of
        Just proof -> return $ ProofCommand UnfoldCmd proof

makeBinary:: String -> Fom -> Fom -> Fom
makeBinary str a b = FunFom OFun (Ident NonePosition str) propType [a, b]

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
        (Nothing, StrategyOriginLeft) -> do
            analyzeError idOrg "ルートスコープ以外では使用できません"
            return StrategyOriginWrong
        (Nothing, StrategyOriginWhole) -> do
            analyzeError idOrg "ルートスコープ以外では使用できません"
            return StrategyOriginWrong
        (Nothing, StrategyOriginAuto) -> do
            analyzeError idOrg "証明の対象が宣言されていません"
            return StrategyOriginWrong
        (_, org) -> return org
    (org , begin) <- buildProofOrigin nOrg
    (list, end) <- buildProofProcessList begin rews
    return $ Proof org list begin end
    where
    buildProofProcessList:: Fom -> [StrategyRewrite] -> Analyzer ([ProofProcess], Fom)
    buildProofProcessList trg [] = return ([], trg)
    buildProofProcessList trg (x:xs) = do
        (proc, goal) <- buildProofProcess trg x
        (rest, end) <- buildProofProcessList goal xs
        return (proc:rest, end)

loadProof:: Rule -> [IdentStm] -> Analyzer Proof
loadProof rule stms = do
    updateVar $ const M.empty
    stg <- buildStrategy stms
    buildProof stg $ Just rule

subScope:: Analyzer a -> Analyzer a
subScope subRountine = do
    emap <- fmap conEnt getContext
    res  <- subRountine
    updateEnt $ const emap
    return res

loadVarDec:: (Ident, Expr) -> Analyzer ()
loadVarDec (id, exp) = do
    mFom <- buildFom exp
    maybe (return ()) (insertEnt False id) mFom

loadVarDecs:: [[(Ident, Expr)]] -> Analyzer ()
loadVarDecs = mapM_ (mapM_ loadVarDec)

loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem decs prop stms) = do
    (prf, mRule) <- subScope $ do
        loadVarDecs decs
        mRule <- buildRule prop
        prf <- maybe (return Nothing) (\rule-> Just <$> loadProof rule stms) mRule
        return (prf, mRule)
    maybe (return ()) (\rule-> insertRule rule{ruleProof=prf}) mRule

loadDecla (Axiom decs prop) = do
    mRule <- subScope $ do
        loadVarDecs decs
        buildRule prop
    maybe (return ()) insertRule mRule

loadDecla (Undef id ty mTex) = do
    mTy <- buildFom ty
    maybe (return ()) (\ty-> insertEntWithLatex True id ty mTex) mTy
    
loadDecla (Define id decs ret def) = subScope $ do
    loadVarDecs decs
    mArgTys <- mapM (buildFom . snd) (last decs)
    mRetTy <- buildFom ret
    case (conjMaybe mArgTys, mRetTy) of
        (Just argTys, Just retTy) -> do
            let ty = FunTypeFom { funTypeIdent = id, funArgTypes = argTys, funRetType = retTy }
            insertEnt True id ty
        _ -> return ()

loadDecla (DataType id def) = do
    insertEnt True id TypeOfType
    mapM_ insertCstr $ extractArgs "|" def
    where
    tyFom = makeType (idStr id)
    insertCstr:: Expr -> Analyzer ()
    insertCstr (IdentExpr id) = insertEnt True id tyFom
    insertCstr (FunExpr id args) = do
        mArgs <- mapM buildFom args
        mapM_ checkType mArgs
        case conjMaybe mArgs of
            Just args -> do
                let ty = FunTypeFom { funTypeIdent=id, funArgTypes=args, funRetType=tyFom }
                insertEnt True id ty
            Nothing -> return ()
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