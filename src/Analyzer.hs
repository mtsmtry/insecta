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

isAssociative:: Fom -> Fom -> Bool
isAssociative bf@FunFom{} af@FunFom{} = case (funArgs bf, funArgs af) of
    ([a, b], [c, d]) -> funName bf == funName af && a == c && b == d
    _ -> False
isAssociative _ _ = False

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
    sameName (x:xs) = let name = funName x in all (\x-> name == funName x) xs
isCommutative _ _ = False

data BuildFomOption = AllowUndefined | NotAllowUndefined deriving(Eq, Show)

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
                then return $ Just $ CstFom id UnknownFom
                else analyzeErrorM id "Not defined"

    buildFom (FunExpr id@(Ident pos "->") [arg, ret]) = do
        mArgs <- mapM buildFom (extractFromTuple arg)
        mRet <- buildFom ret
        return $ FunTypeFom id <$> (conjMaybe mArgs) <*> mRet
      where
        extractFromTuple:: Expr -> [Expr]
        extractFromTuple (FunExpr (Ident _ "tuple") args) = args
        extractFromTuple fom = [fom]

    buildFom e@(FunExpr id@(Ident pos fun) args) = do
        mEnt <- lookupEnt fun
        mArgs <- mapM buildFom args
        maybeFlip mEnt (analyzeErrorM id "Not defined") $ \ent-> do
            let ty = entType ent
            checkFunc ty mArgs
            return $ FunFom OFun id ty <$> (conjMaybe mArgs)
      where
        checkFunc:: Fom -> [Maybe Fom] -> Analyzer Bool
        checkFunc (FunTypeFom _ argTys retTy) argVls = if length argTys /= length argVls
                then analyzeErrorB id "Argument number wrong"
                else do
                    mapM_ (uncurry checkType) $ zip argVls argTys
                    return False
        checkFunc _ _ = analyzeErrorB id $ "Not function:" ++ idStr id
        checkType:: Maybe Fom -> Fom -> Analyzer ()
        checkType (Just vl) ty = let vlTy = evalType vl in unless (vlTy == ty || vlTy == UnknownFom) $ do
            eStr <- onOpeMap showFom vlTy
            aStr <- onOpeMap showFom ty
            let msg = "Couldn't match expected type '" ++ eStr ++ "' with actual type '" ++ aStr ++ "'"
            analyzeError (showIdent vl) msg
        checkType _ _ = return ()

    buildFom _ = return Nothing -- error $ "Wrong pattern:" ++ show e 

getLabel:: Maybe Fom -> Maybe String
getLabel (Just fun@FunFom{}) = Just $ idStr $ funName fun
getLabel Nothing = Nothing

buildRule:: Expr -> Analyzer (Maybe Rule)
buildRule (FunExpr id@(Ident _ "=>") [bf, af]) = do
    let checkType (Just fom) = when (evalType fom /= makeType "Prop") (analyzeError (funName fom) "This is not prop")
        checkType Nothing = return ()
    bfFom <- buildFom bf
    afFom <- buildFom af
    checkType bfFom
    checkType afFom
    return $ Rule SimpRule id Nothing <$> getLabel bfFom <*> bfFom <*> afFom

buildRule (FunExpr id@(Ident _ ">>=") [bf, af]) = do
    let checkType (Just bf) (Just af) = evalType bf == evalType af
        checkType _ _ = False
    bfFom <- buildFom bf
    afFom <- buildFom af
    if checkType bfFom afFom
        then return $ Rule ImplRule id Nothing <$> getLabel bfFom <*> bfFom <*> afFom
        else analyzeErrorM id "error"

buildRule expr = analyzeErrorM (showExprIdent expr) "Invaild rule"

returnMessage:: a -> Message -> Analyzer a
returnMessage a m = Analyzer $ \ctx-> ([m], ctx, a)

insertRule:: Rule -> Analyzer ()
insertRule rule = case ruleKind rule of
    SimpRule -> do
        insertSimp (ruleIdent rule) (ruleBf rule) (ruleAf rule)
        updateSimp $ M.insertWith (++) (ruleLabel rule) [rule]
    ImplRule -> updateImpl $ M.insertWith (++) (ruleLabel rule) [rule]

loadRule:: Expr -> Maybe Proof -> Analyzer ()
loadRule exp prf = do
    mRule <- buildRule exp
    case mRule of
        Just rule -> insertRule rule{ruleProof=prf}
        Nothing -> return ()

buildCmd:: IdentCmd -> Analyzer Command
buildCmd (IdentCmd id StepCmd) = return StepCmd
buildCmd (IdentCmd id ImplCmd) = return ImplCmd
buildCmd (IdentCmd id UnfoldCmd) = return UnfoldCmd
buildCmd (IdentCmd id _) = do
    analyzeErrorM id "Invaild command"
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
buildStrategy (IdentStm id x:xs) = case x of
    (CmdStm (IdentCmd _ BeginCmd) exp) -> do
        fom <- buildFom exp
        rew <- buildStrategyRewriteList xs
        let org = maybe StrategyOriginWrong StrategyOriginFom fom
        return $ Strategy org rew
    (CmdStm (IdentCmd _ TargetCmd) exp) -> do
        rew <- buildStrategyRewriteList xs
        org <- case exp of
            (IdentExpr (Ident _ "left")) -> return StrategyOriginLeft
            exp -> do
                fom <- buildFom exp
                return $ maybe StrategyOriginWrong StrategyOriginContext fom
        return $ Strategy org rew
    _ -> do
        analyzeError id "This is not proof begin"
        rew <- buildStrategyRewriteList xs
        return $ Strategy StrategyOriginWrong rew
  where
    buildStrategyRewriteList xs = extractMaybe <$> mapM buildStrategyRewrite xs

buildProofOrigin:: StrategyOrigin -> Analyzer (ProofOrigin, Fom)
buildProofOrigin (StrategyOriginContext con) = do
    let props = extractArgs "&" con
    preds <- conjMaybe <$> mapM checkCon props
    return (maybe ProofOriginWrong ProofOriginContext preds, con)
  where
    checkCon:: Fom -> Analyzer (Maybe (Entity, Fom))
    checkCon (PredFom pred ty) = do
        mEnt <- lookupEnt $ idStr pred
        case mEnt of
            Just ent -> if entType ent == ty
                then return $ Just (ent, ty)
                else analyzeErrorM pred "Wrong type"
            Nothing -> analyzeErrorM pred "Not found on context"
    checkCon fom = analyzeErrorM (showIdent fom) "Not pred"
    extractArgs:: String -> Fom -> [Fom]
    extractArgs str fun@FunFom{} = if str == idStr (funName fun)
        then concatMap (extractArgs str) (funArgs fun)
        else [fun]
    extractArgs str expr = [expr]

buildProofCommand:: Fom -> Command -> Fom -> Analyzer ProofCommand
buildProofCommand trg StepCmd goal = do
    sTrg <- simplify trg
    sGoal <- simplify goal
    case mergeRewrite sTrg sGoal of
        Just proof -> return $ ProofCommand StepCmd proof
        Nothing -> do
            strTrg <- onOpeMap showLatestFom sTrg
            strGoal <- onOpeMap showLatestFom sGoal
            let msg = "Couldn't match simplified terms with '" ++ strTrg ++ "' and '" ++ strGoal ++ "'"
            analyzeError (showIdent goal) msg
            return $ ProofCommand StepCmd goal

buildProofCommand trg ImplCmd goal = do
    res <- derivate (trg, goal)
    case res of
        Just proof -> return $ ProofCommand ImplCmd proof
        Nothing -> do
            str <- onOpeMap showLatestFom goal
            analyzeError (showIdent goal) $ "Couldn't derivate from '" ++ str ++ "'"
            return $ ProofCommand ImplCmd goal

buildProofCommand trg UnfoldCmd goal = do
    res <- derivateUnfold (trg, goal)
    case res of
        Just proof -> return $ ProofCommand UnfoldCmd proof

buildProofProcess:: Fom -> StrategyRewrite -> Analyzer (ProofProcess, Fom)
buildProofProcess trg (CmdRewrite cmd goal) = do
    proc <- buildProofCommand trg cmd goal
    return (CmdProcess proc, goal)

buildProofProcess trg (AssumeRewrite cmd assume main) = do
    let implies a b = FunFom OFun (Ident NonePosition "=>") propType [a, b]
    mainProof <- buildProof main
    let firstFom = implies assume (prfBegin mainProof)
    proofCmd <- buildProofCommand trg cmd firstFom
    let lastFom = implies assume (prfEnd mainProof)
    return (AssumeProcess proofCmd assume mainProof, lastFom)

buildProof:: Strategy -> Analyzer Proof
buildProof (Strategy stOrg rews) = do
    (org , begin) <- buildProofOrigin stOrg
    (list, end  ) <- buildProofProcessList begin rews
    return $ Proof org list begin end
  where
    buildProofProcessList:: Fom -> [StrategyRewrite] -> Analyzer ([ProofProcess], Fom)
    buildProofProcessList trg (x : xs) = do
        (proc, goal) <- buildProofProcess trg x
        (rest, end ) <- buildProofProcessList goal xs
        return (proc : rest, end)

loadProof:: [IdentStm] -> Analyzer Proof
loadProof stms = do
    updateVar $ const M.empty
    buildStrategy stms >>= buildProof

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

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem decs prop stms) = subScope $ do
    loadVarDecs decs
    prf <- loadProof stms
    loadRule prop (Just prf)

loadDecla (Axiom decs prop) = subScope $ do
    loadVarDecs decs
    loadRule prop Nothing

loadDecla (Undef id ty mTex) = do
    mTy <- buildFom ty
    maybe (return ()) (insertEnt True id) mTy
    
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
            Just args -> return FunTypeFom { funTypeIdent=id, funArgTypes=args, funRetType=TypeOfType }
            Nothing -> return Nothing
      where
        checkType:: Maybe Fom -> Analyzer ()
        checkType (Just fom) = when (evalType fom /= TypeOfType) (analyzeError id "This is not Type")
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