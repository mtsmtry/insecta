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

simplifyM:: Fom -> Analyzer Fom
simplifyM fom = do
    simp <- fmap conSimp getContext
    list <- fmap conList getContext
    return $ simplify list simp fom

derivateM:: (Fom, Fom) -> Analyzer (Maybe Fom)
derivateM pair = do
    impl <- fmap conImpl getContext
    return $ derivate impl pair

buildFom:: Expr -> Analyzer (Maybe Fom)
buildFom (NumExpr num) = return $ Just $ NumFom num
buildFom (StrExpr str) = return $ Just $ StrFom str

buildFom (IdentExpr id) = do
    mEnt <- lookupEnt $ idStr id
    maybeFlip mEnt (analyzeErrorM id "Not defined") $ \ent->
        return $ Just $ VarFom id (entType ent)

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
    checkType (Just vl) ty = let vlTy = evalType vl in unless (vlTy == ty) $ do
        eStr <- onOpeMap showFom vlTy
        aStr <- onOpeMap showFom ty
        let msg = "Couldn't match expected type '" ++ eStr ++ "' with actual type '" ++ aStr ++ "'"
        analyzeError (showIdent vl) msg
    checkType _ _ = return ()
    
buildFom e = return Nothing -- error $ "Wrong pattern:" ++ show e 

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

buildCmd:: IdentCmd -> Analyzer ProofCmd
buildCmd (IdentCmd id StepCmd) = return StepProofCmd
buildCmd (IdentCmd id ImplCmd) = return ImplProofCmd
buildCmd (IdentCmd id UnfoldCmd) = return UnfoldProofCmd
buildCmd (IdentCmd id _) = do
    analyzeErrorM id "Invaild command"
    return WrongProofCmd

buildProofRewrite:: IdentStm -> Analyzer (Maybe ProofRewrite)
buildProofRewrite (IdentStm id (CmdStm idCmd exp)) = do
    fom <- buildFom exp
    cmd <- buildCmd idCmd
    let proof = CmdProof cmd <$> fom
    return $ Just $ fromMaybe WrongProof proof

buildProofRewrite (IdentStm id (AssumeStm idCmd assume stm)) = do
    cmd <- buildCmd idCmd
    fom <- buildFom assume
    block <- buildProof stm
    let proof = AssumeProof cmd <$> fom <*> Just block
    return $ Just $ fromMaybe WrongProof proof

buildProofRewrite (IdentStm id (ForkStm list)) = do
    forks <- mapM buildFork list
    return $ Just $ ForkProof forks
    where
    buildFork:: (IdentCmd, [IdentStm]) -> Analyzer (ProofCmd, Proof)
    buildFork (idCmd, stms) = do
        cmd <- buildCmd idCmd
        block <- buildProof stms
        return (cmd, block)

buildProofRewrite (IdentStm id (ForAllStm var ty)) = do
    mFom <- buildFom ty
    case mFom of
        Just fom -> updateVar $ M.insert (idStr var) $ Variable ForAll fom
        Nothing -> return ()
    return Nothing

buildProofRewrite (IdentStm id (ExistsStm var refs ty)) = do
    mFom <- buildFom ty
    case mFom of
        Just fom -> updateVar $ M.insert (idStr var) $ Variable (Exists refs) fom
        Nothing -> return ()
    return Nothing

buildProof:: [IdentStm] -> Analyzer Proof
buildProof (IdentStm id x:xs) = case x of
    (CmdStm (IdentCmd _ BeginCmd) exp) -> do
        fom <- buildFom exp
        rew <- buildProofRewriteList xs
        let org = maybe ProofOriginWrong ProofOriginFom fom
        return $ Proof org rew
    (CmdStm (IdentCmd _ TargetCmd) exp) -> do 
        rew <- buildProofRewriteList xs
        trg <- case exp of
            (IdentExpr (Ident _ "left")) -> return $ Just ProofTrgLeft
            (IdentExpr (Ident _ "context")) -> return $ Just ProofTrgContext
            exp -> analyzeErrorM (showExprIdent exp) "Not exist"
        let org = maybe ProofOriginWrong ProofOriginTrg trg
        return $ Proof org rew
    _ -> do
        analyzeError id "This is not proof begin"
        rew <- buildProofRewriteList xs
        return $ Proof ProofOriginWrong rew
    where
    buildProofRewriteList xs = extractMaybe <$> mapM buildProofRewrite xs

buildProofEnv:: [IdentStm] -> Analyzer ProofEnv
buildProofEnv stms = do
    updateVar $ const M.empty
    proof <- buildProof stms
    vmap <- fmap conVar getContext
    return $ ProofEnv proof vmap

analyzeProofRewrite:: Fom -> ProofRewrite -> Analyzer Fom
analyzeProofRewrite trg (CmdProof StepProofCmd goal) = do
    sTrg <- simplifyM trg
    sGoal <- simplifyM goal
    case mergeRewrite sTrg sGoal of
        Just proof -> return sGoal
        Nothing -> do
            strTrg <- onOpeMap showLatestFom sTrg
            strGoal <- onOpeMap showLatestFom sGoal
            let msg = "Couldn't match simplified terms with '" ++ strTrg ++ "' and '" ++ strGoal ++ "'"
            analyzeError (showIdent goal) msg
            return sGoal

analyzeProofRewrite trg (CmdProof ImplProofCmd goal) = do
    res <- derivateM (trg, goal)
    case res of
        Just proof -> return proof
        Nothing -> do
            str <- onOpeMap showLatestFom goal
            analyzeError (showIdent goal) $ "Couldn't derivate from '" ++ str ++ "'"
            return goal

-- analyzeProofRewrite trg (CmdProof UnfoldProofCmd goal) = do

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