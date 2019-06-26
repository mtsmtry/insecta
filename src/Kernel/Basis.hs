module Kernel.Basis where
import Kernel.Data
import Common.Monad
import Common.Data
import qualified Data.Map as M

makeBinary:: String -> Fom -> Fom -> Fom
makeBinary str a b = Fom $ FunFom OFun (Ident str) propType [a, b]

typeAs:: String -> Fom
typeAs str = Fom $ VarFom{varFomId=Ident str, varFomTy=typeFom}

propType:: Fom
propType = typeAs "Prop"

latestFom:: RewFom -> Fom
latestFom rew@Rewrite{} = latestFom $ rewLater rew
latestFom (RewFom fun@FunFom{}) = Fom fun{funArgs=map latestFom $ funArgs fun}
latestFom fom = toFom fromRew fom

oldestFom:: RewFom -> Fom
oldestFom rew@Rewrite{} = oldestFom $ rewOlder rew
oldestFom (RewFom fun@FunFom{}) = Fom fun{funArgs=map latestFom $ funArgs fun}
oldestFom fom = toFom fromRew fom

(<||>):: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a)
a <||> b = \m-> a m <|> b m

applyArgsOnce:: (Fom -> Maybe Fom) -> Fom -> Maybe Fom
applyArgsOnce apply (Fom fun@FunFom{}) = do
    args <- applyOnce (funArgs fun) []
    return $ Fom fun{funArgs=args}
    where
    applyOnce:: [Fom] -> [Fom] -> Maybe [Fom]
    applyOnce [] _ = Nothing
    applyOnce (a:as) as' = maybe (applyOnce as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (apply a)

evalTy:: Fom -> Fom
evalTy (Fom (AtomFom atom)) = evalTyAtom atom where
    evalTyAtom:: AtomFom -> Fom
    evalTyAtom StrFom{} = typeAs "String"
    evalTyAtom NatFom{} = typeAs "N"
    evalTyAtom SubTypeFom{} = typeFom
    evalTyAtom TypeOfType = error "evalTy TypeOfType"
evalTy (Fom (VarFom _ ty)) = ty
evalTy (Fom fom@FunFom{}) = funTy fom
evalTy (Fom FunTyFom{}) = typeFom
evalTy (Fom PredTyFom{}) = typeFom
evalTy (Fom PredFom{}) = typeAs "Prop"

unify:: PtnFom -> Fom -> Maybe AssignMap
unify _ptn _trg = unifyWithAsg _ptn _trg M.empty where
    unifyFun:: ([PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap) -> PtnFom -> Fom -> AssignMap -> Maybe AssignMap
    unifyFun unifyArgs (PtnFom ptn) (Fom trg) = if funTy ptn == funTy trg && funId ptn == funId trg 
        then unifyArgs (funArgs ptn) (funArgs trg)
        else const Nothing

    unifyArgsRandom:: ([Fom] -> AssignMap -> Maybe AssignMap) -> [PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgsRandom restInserter = unifyArgs where
        unifyArgs:: [PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap
        unifyArgs [] rests = restInserter rests
        unifyArgs (ptn:ptns) trgs = matchForPtn ptn ptns [] trgs
        matchForPtn:: PtnFom -> [PtnFom] -> [Fom] -> [Fom] -> AssignMap -> Maybe AssignMap
        matchForPtn ptn ptns noMatchTrgs [] = const Nothing
        matchForPtn ptn ptns noMatchTrgs (trg:restTrgs) = main <||> rest where
            main = unifyWithAsg ptn trg >=> unifyArgs ptns (noMatchTrgs ++ restTrgs)
            rest = matchForPtn ptn ptns (noMatchTrgs ++ [trg]) restTrgs
    unifyArgsOrder:: [PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgsOrder ptns args = if length ptns /= length args 
        then return Nothing
        else unifyArgs ptns args
        where
        unifyArgs:: [PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap
        unifyArgs (e:ex) (e':ex') = unifyWithAsg e e' >=> unifyArgs ex ex'
        unifyArgs [] [] = Just
        unifyArgs _ _ = const Nothing
    unifyArgsComm:: [PtnFom] -> [Fom] -> AssignMap -> Maybe AssignMap
    unifyArgsComm [a, b] [a', b'] = (unifyWithAsg a a' >=> unifyWithAsg b b') <||> (unifyWithAsg a b' >=> unifyWithAsg b a')

    checkOrInsert:: Ident -> Fom -> AssignMap -> Maybe AssignMap
    checkOrInsert name fom m = case M.lookup name m of
        Just x -> if x == fom then Just m else Nothing
        Nothing -> Just $ M.insert name fom m

    toFunFom:: AssignMap -> PtnFom -> PtnFom
    toFunFom m (ACInsertFom isrtName fom) = case M.lookup isrtName m of
        Just fom@(Fom fun@FunFom{})
            | funId fun == funId ptn -> PtnFom ptn{funArgs=(map RawVarFom $ funArgs fun) ++ funArgs ptn}
            | otherwise -> PtnFom ptn{funArgs=RawVarFom fom:funArgs ptn}
        Just fom -> PtnFom ptn{funArgs=RawVarFom fom:funArgs ptn}
        where PtnFom ptn = toFunFom m fom
    toFunFom m fom = fom

    unifyWithAsg:: PtnFom -> Fom -> AssignMap -> Maybe AssignMap
    unifyWithAsg (PtnFom (AtomFom ptn)) (Fom (AtomFom trg)) = if ptn == trg then Just else const Nothing
    unifyWithAsg (PtnFom (VarFom id ty)) (Fom (VarFom id' ty')) = if id == id' then unifyWithAsg ty ty' else const Nothing
    unifyWithAsg (PtnFom (PredFom trgVl trgTy)) (Fom (PredFom ptnVl ptnTy)) = unifyWithAsg trgVl ptnVl >=> unifyWithAsg trgTy ptnTy
    unifyWithAsg (PtnFom ptn@(VarFom id ty)) trg = checkOrInsert id trg
    unifyWithAsg ptn@(PtnFom FunFom{}) trg@(Fom fun@FunFom{}) = case funAttr fun of
        OFun -> unifyFun unifyArgsOrder ptn trg
        CFun -> unifyFun unifyArgsComm ptn trg
        AFun -> unifyFun unifyArgsOrder ptn trg
        ACFun -> unifyFun (unifyArgsRandom $ \case []-> Just; _-> const Nothing) ptn trg
    unifyWithAsg ptn@ACInsertFom{} trg@(Fom FunFom{}) = \m-> unifyWithAsg (toFunFom m ptn) trg m
    unifyWithAsg (ACRestFom restName ptn) trg@(Fom trgFun@FunFom{}) = \m-> unifyFun (unifyArgsRandom inserter) (toFunFom m ptn) trg m where
        inserter:: [Fom] -> AssignMap -> Maybe AssignMap
        inserter [rest] = checkOrInsert restName rest
        inserter rests = checkOrInsert restName $ Fom trgFun{funArgs=rests}
    unifyWithAsg (RawVarFom ptn) trg = if ptn == trg then Just else const Nothing
    unifyWithAsg _ _ = const Nothing

unifyList:: (a -> PtnFom) -> [a] -> Fom -> Maybe (AssignMap, a)
unifyList f (x:xs) trg = case unify (f x) trg of
    Just asg -> Just (asg, x)
    Nothing -> unifyList f xs trg

assign:: AssignMap -> PtnFom -> Fom
assign m ptn@(PtnFom var@(VarFom id ty)) = fromMaybe (toFom fromPtn ptn) $ M.lookup id m
assign m (PtnFom fun@(FunFom ACFun _ _ _)) = case concatMap toArray args of [x]-> x; xs-> Fom fun{funArgs=xs}; where
    args = map (assign m) $ funArgs fun
    toArray:: Fom -> [Fom]
    toArray fom@(Fom arg@FunFom{}) = if funId arg == funId fun then funArgs arg else [fom]
    toArray arg = [arg]
assign m (PtnFom fun@FunFom{}) = Fom fun{funArgs=map (assign m) $ funArgs fun}
assign m ACRestFom{} = error "assign m ACRestFom{}"
assign m (ACEachFom name src (Fom fun) lambda) = case M.lookup name m of 
    Just list -> Fom fun{funArgs=map (applyUnaryLambda lambda m) $ toList list}
    Nothing -> error "not found"
    where
    toList:: Fom -> [Fom]
    toList fom@(Fom trg@FunFom{}) = if src == funId trg then funArgs trg else [fom]
    toList trg = [trg]
    applyUnaryLambda:: UnaryLambda -> AssignMap -> Fom -> Fom
    applyUnaryLambda (UnaryLambda arg body) m value = assign (M.insert arg value m) body
assign m fom = toFom fromPtn fom

toFom:: (ele -> StructFom ele) -> ele -> Fom
toFom f = toFom where
    -- toFom:: ele -> Fom
    toFom = toFom' . f
    -- toFom':: StructFom ele -> Fom
    toFom' (VarFom id ty) = Fom $ VarFom id (toFom ty)
    toFom' fun@FunFom{} = Fom $ fun{funArgs=map toFom (funArgs fun)}
    toFom' (LambdaFom ty args body) = Fom $ LambdaFom (toFom ty) args (toFom body)
    toFom' (FunTyFom id args ty) = Fom $ FunTyFom id args ty
    toFom' (PredTyFom id args base) = Fom $ PredTyFom id (map toFom args) (toFom base)
    toFom' (PredFom vl ty) = Fom $ PredFom (toFom vl) (toFom ty)
    toFom' (AtomFom atom) = Fom $ AtomFom atom