module Analyzer.Formula where
import Kernel.Data

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

    buildFom (FunExpr id@(Ident pos ".") [vl, ty]) = do
        vl <- buildFom vl
        ty <- buildFom ty
        case (vl, evalType <$> vl, ty) of
            (Just vl, Just vlTy, Just pred@PredTypeFom{}) -> when (vlTy /= predTyBase pred) $ do
                strVl <- onOpeMap showFom vl
                strPred <- onOpeMap showFom pred
                strBase <- onOpeMap showFom $ predTyBase pred
                strVlTy <- onOpeMap showFom vlTy
                let msg = "'" ++ strVl ++ "'は述語型'" ++ strPred ++ "'の主語の型'" ++ strBase ++ "'である必要がありますが、実際は'" ++ strVlTy ++ "'型です"
                analyzeError (showIdent vl) msg
            (_, _, Just ty) -> do
                strTy <- onOpeMap showFom ty
                analyzeError (showIdent ty) $ "'" ++ strTy ++ "'は" ++ "述語型ではありません"
            _ -> return ()
        return $ PredFom <$> vl <*> ty

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
            return $ (Just $ PredTypeFom id) <*> conjMaybe args <*> Just (varTy this)
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
            checkType expect pred@PredTypeFom{} = expect == pred || checkType expect (predTyBase pred)
            checkType expect actual = expect == actual || case evalType actual of
                SubTypeFom sub -> checkType expect sub
                _ -> False
        checkType _ _ = return Nothing