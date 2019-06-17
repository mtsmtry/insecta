module Kernel.Basis where
import Kernel.Data

instance Eq Fom where
    a@FunFom{} == b@FunFom{} = sameAttr && case (funAttr a, funAttr b) of
            (ACFun, _) -> equalACFun a b
            (_, ACFun) -> equalACFun a b
            _ -> funArgs a == funArgs b
        where
        sameAttr:: Bool
        sameAttr = funIdent a == funIdent b && funType a == funType b
        equalACFun:: Fom -> Fom -> Bool
        equalACFun a b = equalAsSet (funArgs a) (funArgs b) where
    (PredFom vl ty) == (PredFom vl' ty') = vl == vl' && ty == ty'
    (PredTypeFom id args _) == (PredTypeFom id' args' _) = id == id' && args == args'
    (FunTypeFom id args ret) == (FunTypeFom id' args' ret') = id == id' && args == args' && ret == ret'
    (CstFom a x) == (CstFom b y) = a == b && x == y
    (VarFom a x) == (VarFom b y) = a == b && x == y
    (StrFom a) == (StrFom b) = a == b
    (NumFom a) == (NumFom b) = a == b
    (SubTypeFom a) == (SubTypeFom b) = a == b
    TypeOfType == TypeOfType = True
    UnknownFom == UnknownFom = True
    a == b = False

evalType:: Fom -> Fom
evalType (ACEachFom _ _ fun _) = evalType fun
evalType (ACRestFom _ fun) = evalType fun
evalType (ACInsertFom _ fun) = evalType fun
evalType TypeOfType = error "evalType TypeOfType"
evalType Rewrite{} = error "evalType Rewrite{}"
evalType fom@FunFom{} = funType fom
evalType fom@CstFom{} = cstType fom
evalType fom@VarFom{} = varType fom
evalType StrFom{} = makeType "String"
evalType NumFom{} = makeType "N"
evalType FunTypeFom{} = TypeOfType
evalType PredTypeFom{} = TypeOfType
evalType PredFom{} = makeType "Prop"
evalType fom = error $ show fom

showIdent:: Fom -> Ident
showIdent fom@FunTypeFom{} = funTypeIdent fom
showIdent fom@FunFom{} = funIdent fom
showIdent fom@CstFom{} = cstIdent fom
showIdent fom@VarFom{} = varIdent fom
showIdent (StrFom id) = id
showIdent (NumFom (IdentInt pos num)) = Ident pos (show num)
showIdent fom@PredFom{} = showIdent $ predVl fom
showIdent fom@LambdaFom{} = showIdent $ lambdaBody fom
showIdent fom@PredTypeFom{} = predTyName fom
showIdent (RawVarFom raw) = showIdent raw
showIdent UnknownFom = Ident NonePosition "unknown"
showIdent fom = error $ show fom

unify:: Fom -> Fom -> Maybe AssignMap
unify ptn trg = unifyWithAsg ptn trg M.empty

unifyFun:: ([Fom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyFun unifyArgs ptn trg = if funIdent ptn /= funIdent trg then const Nothing else \m-> do
    tyAsg <- unifyWithAsg (funType ptn) (funType trg) m
    vlAsg <- unifyArgs (funArgs ptn) (funArgs trg) tyAsg
    return $ M.union tyAsg vlAsg

unifyArgsOrder:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyArgsOrder ptns args = if length ptns /= length args 
    then return Nothing
    else unifyArgs ptns args
    where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs (e:ex) (e':ex') = unifyWithAsg e e' >=> unifyArgs ex ex'
    unifyArgs [] [] = Just
    unifyArgs _ _ = const Nothing

unifyArgsRandom:: ([Fom] -> AssignMap -> Maybe AssignMap) -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
unifyArgsRandom restInserter = unifyArgs where
    unifyArgs:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgs [] rests = restInserter rests
    unifyArgs (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs
    matchForPtn:: Fom -> [Fom] -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    matchForPtn ptn ptns noMatchTrgs [] = const Nothing
    matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
        main = unifyWithAsg ptn trg >=> unifyArgs ptns (noMatchTrgs ++ restTrgs)
        rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs

checkInsert:: String -> Fom -> AssignMap -> Maybe AssignMap
checkInsert name fom = \m-> case M.lookup name m of
    Just x -> if x == fom then Just m else Nothing
    Nothing -> Just $ M.insert name fom m

toFunFom:: AssignMap -> Fom -> Fom
toFunFom m (ACInsertFom isrtName fom) = case M.lookup isrtName m of
    Just fun@FunFom{}
        | funIdent fun == funIdent ptn -> ptn{funArgs=(map RawVarFom $ funArgs fun) ++ funArgs ptn}
        | otherwise -> ptn{funArgs=RawVarFom fun:funArgs ptn}
    Just fom -> ptn{funArgs=RawVarFom fom:funArgs ptn}
    where ptn = toFunFom m fom
toFunFom m fom = fom

unifyWithAsg:: Fom -> Fom -> AssignMap -> Maybe AssignMap
unifyWithAsg Rewrite{} _ = const $ error "Do not use Rewrite in a rule"
unifyWithAsg ptn trg@Rewrite{} = unifyWithAsg ptn $ rewLater trg
unifyWithAsg TypeOfType TypeOfType = Just
unifyWithAsg ptn@(CstFom id ty) trg@(CstFom id' ty') = if id == id' then unifyWithAsg ty ty' else const Nothing
unifyWithAsg ptn@NumFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg ptn@StrFom{} trg = if ptn == trg then Just else const Nothing
unifyWithAsg (PredFom trgVl trgTy) (PredFom ptnVl ptnTy) = unifyWithAsg trgVl ptnVl >=> unifyWithAsg trgTy ptnTy
unifyWithAsg (RawVarFom ptn) trg = if ptn == trg then Just else const Nothing
unifyWithAsg ptn@(VarFom id ty) trg = checkInsert (idStr id) (latestFom trg) 
unifyWithAsg ptn@FunFom{} trg@FunFom{} = case funAttr trg of
    OFun -> unifyFun unifyArgsOrder ptn trg
    CFun -> unifyFun unifyArgsComm ptn trg
    AFun -> unifyFun unifyArgsOrder ptn trg
    ACFun -> unifyFun (unifyArgsRandom $ \case []-> Just; _-> const Nothing) ptn trg
    where
    unifyArgsComm:: [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgsComm [a, b] [a', b'] = (unifyWithAsg a a' >=> unifyWithAsg b b') <||> (unifyWithAsg a b' >=> unifyWithAsg b a')
unifyWithAsg ptn@ACInsertFom{} trg@FunFom{} = \m-> unifyWithAsg (toFunFom m ptn) trg m
unifyWithAsg (ACRestFom restName ptn) trg@FunFom{} = \m-> unifyFun (unifyArgsRandom inserter) (toFunFom m ptn) trg m where
    inserter [rest] = checkInsert restName rest
    inserter rests = checkInsert restName trg{funArgs=rests}
unifyWithAsg _ _ = const Nothing

unifyList:: (a -> Fom) -> [a] -> Fom -> Maybe (AssignMap, a)
unifyList f (x:xs) trg = case unify (f x) trg of
    Just asg -> Just (asg, x)
    Nothing -> unifyList f xs trg

assign:: AssignMap -> Fom -> Fom
assign m var@(VarFom id ty) = fromMaybe var $ M.lookup (idStr id) m
assign m fun@(FunFom ACFun _ _ _) = case concatMap toArray args of [x]-> x; xs-> fun{funArgs=xs}; where
    args = map (assign m) $ funArgs fun
    toArray arg@FunFom{} = if funIdent arg == funIdent fun then funArgs arg else [arg]
    toArray arg = [arg]
assign m fom@FunFom{} = applyArgs (assign m) fom
assign m ACRestFom{} = error "assign m ACRestFom{}"
assign m (ACEachFom name src fun lambda) = case M.lookup name m of 
    Just list -> fun{funArgs=map (applyUnaryLambda lambda m) $ toList list}
    Nothing -> error "not found"
    where
    toList trg@FunFom{} = if src == (idStr $ funIdent trg) then funArgs trg else [trg]
    toList trg = [trg]
assign m fom = fom

applyUnaryLambda:: UnaryLambda -> AssignMap -> Fom -> Fom
applyUnaryLambda (UnaryLambda arg body) m value = assign (M.insert arg value m) body
