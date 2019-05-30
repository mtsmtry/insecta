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
getLabel  Nothing = Nothing

buildRule:: Expr -> Analyzer (Maybe Rule)
buildRule (FunExpr id@(Ident _ "=>") [bf, af]) = do
    let checkType (Just fom) = when (evalType fom /= makeType "Prop") (analyzeError (funName fom) "This is not prop")
        checkType Nothing = return ()
    bfFom <- buildFom bf
    afFom <- buildFom af
    checkType bfFom
    checkType afFom
    return $ Rule SimpRule id <$> getLabel bfFom <*> bfFom <*> afFom

buildRule (FunExpr id@(Ident _ ">>=") [bf, af]) = do
    let checkType (Just bf) (Just af) = evalType bf == evalType af
        checkType _ _ = False
    bfFom <- buildFom bf
    afFom <- buildFom af
    if checkType bfFom afFom 
        then return $ Rule ImplRule id <$> getLabel bfFom <*> bfFom <*> afFom
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

buildCmd:: IdentCmd -> Analyzer Command
buildCmd (IdentCmd id StepCmd) = return Command
buildCmd (IdentCmd id ImplCmd) = return ImplCmd
buildCmd (IdentCmd id UnfoldCmd) = return UnfoldCmd
buildCmd (IdentCmd id _) = do
    analyzeErrorM id "Invaild command"
    return WrongProofCmd

buildStrategyRewrite:: IdentStm -> Analyzer (Maybe StrategyRewrite)
buildStrategyRewrite (IdentStm id (CmdStm idCmd exp)) = do
    cmd <- buildCmd idCmd
    fom <- if cmd == UnfoldProofCmd then buildFomEx AllowUndefined exp else buildFom exp
    let proof = CmdProof cmd <$> fom
    return $ Just $ fromMaybe WrongProof proof

buildStrategyRewrite (IdentStm id (AssumeStm idCmd assume stm)) = do
    cmd <- buildCmd idCmd
    fom <- buildFom assume
    block <- buildStrategy stm
    let proof = AssumeProof cmd <$> fom <*> Just block
    return $ Just $ fromMaybe WrongProof proof

buildStrategyRewrite (IdentStm id (ForkStm list)) = do
    forks <- mapM buildFork list
    return $ Just $ ForkProof forks
    where
    buildFork:: (IdentCmd, [IdentStm]) -> Analyzer (Command, Proof)
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
        let org = maybe ProofOriginWrong ProofOriginFom fom
        return $ Proof org rew
    (CmdStm (IdentCmd _ TargetCmd) exp) -> do 
        rew <- buildStrategyRewriteList xs
        trg <- case exp of
            (IdentExpr (Ident _ "left")) -> return $ Just ProofTrgLeft
            (IdentExpr (Ident _ "context")) -> return $ Just ProofTrgContext
            exp -> analyzeErrorM (showExprIdent exp) "Not exist"
        let org = maybe ProofOriginWrong ProofOriginTrg trg
        return $ Proof org rew
    _ -> do
        analyzeError id "This is not proof begin"
        rew <- buildStrategyRewriteList xs
        return $ Proof ProofOriginWrong rew
    where
    buildStrategyRewriteList xs = extractMaybe <$> mapM buildStrategyRewrite xs

-- buildStrategyEnv:: [IdentStm] -> Analyzer ProofEnv
buildStrategyEnv stms = do
    updateVar $ const M.empty
    proof <- buildStrategy stms
    vmap <- fmap conVar getContext
    return $ ProofEnv proof vmap

buildStrategyOrigin:: StrategyOrigin -> Analyzer ProofOrigin
buildStrategyOrigin (StrategyOriginTrg (StrategyTrgContext con)) = do
    let props = extractArgs "&" con
    preds <- mapM checkCon props
    return con
    where
    checkCon:: Fom -> Analyzer (Maybe (Entity, Fom))
    checkCon (PredFom pred ty) = do
        ent <- lookupEnt pred
        if entType ent == ty
            then return $ Just (ent, ty)
            else analyzeErrorM pred "Not found on context"
    checkCon fom = analyzeError (showIdent fom) "Not pred"

buildProofCommand:: Fom -> Command -> Fom -> Analyzer ProofCommand
buildProofCommand trg StepCmd goal = do
    sTrg <- simplify trg
    sGoal <- simplify goal
    case mergeRewrite sTrg sGoal of
        Just proof -> return $ ProofCommand trg StepCmd goal
        Nothing -> do
            strTrg <- onOpeMap showLatestFom sTrg
            strGoal <- onOpeMap showLatestFom sGoal
            let msg = "Couldn't match simplified terms with '" ++ strTrg ++ "' and '" ++ strGoal ++ "'"
            analyzeError (showIdent goal) msg
            return sGoal

buildProofCommand trg ImplCmd goal = do
    res <- derivate (trg, goal)
    case res of
        Just proof -> return proof
        Nothing -> do
            str <- onOpeMap showLatestFom goal
            analyzeError (showIdent goal) $ "Couldn't derivate from '" ++ str ++ "'"
            return goal

buildProofCommand trg UnfoldCmd goal = do
    res <- derivateUnfold (trg, goal)
    case res of
        Just proof -> return proof

buildProofProcess:: Fom -> StrategyRewrite -> Analyzer (ProofProcess, Fom)
buildProofProcess trg (CmdRewrite cmd goal) = do
    proc <- buildProofCommand trg cmd goal
    return (maybe WrongProcess CmdProcess proc, goal)

buildProofProcess trg (AssumeRewrite cmd assume main) = do
    let implies a b = FunFom OFun (Ident NonePosition "=>") propType [a, b]
    proof <- buildProof main
    let fom = implies assume main
    proofCmd <- buildProofCommand trg cmd (oldestFom fom)
    let result = implies assume (latestFom proof)
    return (AssumeProcess proofCmd assume proof, result)

buildProof:: Strategy -> Analyzer Proof
buildProof (ProofStrategy orgn rews) = do
    buildProofProcess 

subScope::Analyzer a -> Analyzer a
subScope subRountine = do
    tmap <- fmap ctxScope getContext
    res <- subRountine
    updateScope $ const tmap
    return res

loadVarDec:: (Ident, Fom) -> Analyzer ()
loadVarDec (id, tFom) = do
    mnt <- buildFom tFom
    maybe (return ()) (addIdent False id) mnt

-- reflect a declaration in the global scope and analyze type and proof
loadDecla:: Decla -> Analyzer ()
loadDecla (Theorem decs prop stm) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    mnprop <- buildFom prop
    maybeFlip mnprop (return ()) $ \nprop-> do
        case nprop of
            (FunFom _ [start, _]) -> return () -- Just <$> runStatement start stm
            _ -> analyzeError (showIdent prop) "Not function"
        insertRule nprop

loadDecla (Axiom decs prop) = subScope $ do
    mapM_ (mapM_ loadVarDec) decs
    insertRule prop

loadDecla (Undef id tFom mtex) = do
    mnt <- buildFom tFom
    maybe (return ()) (addIdent True id) mnt
    case mtex of 
        Just tex -> updateLatex $ M.insert (show id) tex
        Nothing -> return ()

loadDecla (Define t args ret def) = do
    subScope $ do
        mapM_ (mapM_ loadVarDec) args
    addIdent True t (makeFuncType (map snd (head args)) ret)

loadDecla (DataType id def) = do
    insertEnt True id TypeOfType
    mapM_ insertCstr $ extractArgs "|" def
    where
    insertCstr:: Fom -> Analyzer ()
    insertCstr (VarFom id ty) = insertEnt True id ty
    insertCstr (FunExpr id args) = do
        mArgs <- mapM buildFom args
        mapM_ mArgs checkType
        case conjMaybe mArgs of
            Just args -> return FunTypeFom { funTypeIdent=id, funArgTypes=args, funRetType=TypeOfType }
            Nothing -> return Nothing
        where
        checkType (Just fom) = when evalType fom /= TypeOfType $ analyzeError id "This is not Type" 
        checkType Nothing = return ()
    insertCstr e = error $ show e
    -- concat specified function arguments
    -- ex. extractArgs "add" add(add(1, 2), add(3, 4)) => [1, 2, 3, 4]
    extractArgs:: String -> Expr -> [Expr]
    extractArgs str fun@(FunExpr id args) = if str == idStr id then concatMap (extractArgs str) args else [fun]
    extractArgs str expr = [expr]

loadDecla _ = return ()

buildProgram::String -> ([Message], Context)
buildProgram prg = (msg ++ msg', ctx) where
    (msg, declas, omap) = parseProgram prg
    (msg', ctx, _) = analyze (mapM_ loadDecla declas) (newContext omap)