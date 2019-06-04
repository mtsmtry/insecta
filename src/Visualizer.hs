module Visualizer where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Library
import Data

class ToJson a where
    toJson:: a -> Analyzer String

infixl 0 .=
(.=):: k -> v -> (k, v)
key .= value = (key, value)

toJsonMap:: ToJson v => M.Map String v -> Analyzer String
toJsonMap = object . (map (fmap toJson)) . M.toList

object:: [(String, Analyzer String)] -> Analyzer String
object pairs = do
    values <- sequence (map snd pairs)
    let quote v = if head v == '{' && last v == '}' then v else "\"" ++ v ++ "\""
    let body = zipWith (\k v-> "\"" ++ k ++ "\":" ++ quote v) (map fst pairs) values
    return $ "{" ++ intercalate "," body ++ "}"
        
data RewriteList = RewriteFom Fom | RewriteList Reason Fom RewriteList

showRule:: OpeMap -> Rule -> String
showRule omap rule = showFom omap (ruleBf rule) ++ kind ++ showFom omap (ruleAf rule) where
    kind = case ruleKind rule of SimpRule -> " >>= "; ImplRule -> " => "

showReason:: OpeMap -> Reason -> String
showReason omap (NormalReason rule asg) = showRule omap rule ++ toJsonWith (showFom omap) asg
showReason omap EqualReason = ""

toRewriteList:: OpeMap -> Fom -> RewriteList
toRewriteList omap fun@FunFom{}  = build args [] where
    oldest (RewriteFom fom) = fom
    oldest (RewriteList _ _ rest) = oldest rest
    args = map (toRewriteList omap) (funArgs fun)
    build:: [RewriteList] -> [Fom] -> RewriteList
    build [] args = RewriteFom fun{funArgs=args}
    build (RewriteFom e:sargs) args = build sargs (e:args)
    build (RewriteList r old rest:sargs) args = RewriteList r fun{funArgs=(old:map oldest sargs ++ args)} (build (rest:sargs) args)
toRewriteList omap (Rewrite r a b) = add r blist alist where
    alist = toRewriteList omap a
    blist = toRewriteList omap b
    add:: Reason -> RewriteList -> RewriteList -> RewriteList
    add ar (RewriteList r e rest) trg = add ar rest $ RewriteList r e trg
    add ar (RewriteFom fom) trg = RewriteList ar fom trg
toRewriteList omap e = RewriteFom e

showRewriteList:: OpeMap -> RewriteList -> String
showRewriteList omap (RewriteFom e) = showOldestFom omap e
showRewriteList omap (RewriteList r e rest) = showOldestFom omap e
                                            ++ " [" ++ showReason omap r ++ "]" ++ "\n"
                                            ++ showRewriteList omap rest

showRewrites:: OpeMap -> Fom -> String
showRewrites omap fom = showRewriteList omap (toRewriteList omap fom)

showFunFom:: OpeMap -> (OpeMap -> Fom -> String) -> String -> [Fom]-> String
showFunFom omap fshow "tuple" as = "(" ++ intercalate ", " (map (fshow omap) as) ++ ")"
showFunFom omap fshow f args = if isAlpha (head f) 
    then f ++ "(" ++ intercalate ", " (map (fshow omap) args) ++ ")"
    else if getArgNum f == 1 then f ++ fshow omap (head args) else intercalate f (map (fshow omap) args)
    where
    getArgNum h = maybe 2 opeArgNum $ M.lookup h omap
    getPre h = maybe 100 opePreceed $ M.lookup h omap
    bshow fun@FunFom{} = let g = idStr $ funName fun in if length (show g) == 2 && getPre f > getPre (show g) 
        then "(" ++ fshow omap fun ++ ")" 
        else fshow omap fun
    bshow fom = fshow omap fom

showFom:: OpeMap -> Fom -> String
showFom omap (ACEachFom list fun (UnaryLambda arg body)) = list ++ ".each[" ++ idStr (funName fun) ++ "](" ++ arg ++ "->" ++ showFom omap body ++ ")"
showFom omap (ACRestFom rest fun) = "{" ++ rest ++ "}" ++ idStr (funName fun) ++ showFom omap fun
showFom omap (PredFom vl ty) = showFom omap vl ++ "." ++ showFom omap ty
showFom omap UnknownFom = "unknown"
showFom omap TypeOfType = "Type"
showFom omap (StrFom id) = "\"" ++ idStr id ++ "\"" 
showFom omap (NumFom (IdentInt _ num)) = show num
showFom omap (VarFom id _) = idStr id
showFom omap (CstFom id _) = idStr id
showFom omap fun@FunFom{} = showFunFom omap showFom (idStr $ funName fun) (funArgs fun)
showFom omap rew@Rewrite{} = "[" ++ showFom omap (rewOlder rew) ++ ", " ++ showFom omap (rewLater rew) ++ "]"
showFom omap (FunTypeFom id args ret) = argStr ++ "->" ++ showFom omap ret where 
    argStr = case args of
        [arg] -> showFom omap arg
        _ -> "(" ++ intercalate ", " (map (showFom omap) args) ++ ")"

-- showLatex:: OpeMap -> Fom -> String
-- showLatex omap fun@FunFom{} = 

showLatestFom:: OpeMap -> Fom -> String
showLatestFom omap rew@Rewrite{} = showLatestFom omap (rewLater rew)
showLatestFom omap fun@FunFom{} = showFunFom omap showLatestFom (idStr $ funName fun) (funArgs fun)
showLatestFom omap e = showFom omap e

showOldestFom:: OpeMap -> Fom -> String
showOldestFom omap rew@Rewrite{} = showOldestFom omap (rewOlder rew)
showOldestFom omap fun@FunFom{} = showFunFom omap showOldestFom (idStr $ funName fun) (funArgs fun)
showOldestFom omap e = showFom omap e

showFomAsRewrites:: OpeMap -> Fom -> String
showFomAsRewrites omap rew@Rewrite{} = "[" ++ intercalate ", " steps ++ "]" where
    steps = map (showFomAsRewrites omap) $ expandRewrite rew
    expandRewrite:: Fom -> [Fom]
    expandRewrite (Rewrite e a b) = expandRewrite b ++ expandRewrite a
    expandRewrite e = [e]
showFomAsRewrites omap fun@FunFom{} = showFunFom omap showFomAsRewrites (idStr $ funName fun) (funArgs fun)
showFomAsRewrites omap fom = showFom omap fom

evalString:: Expr -> String
evalString e = ""

showMapList:: Show a => (t -> [Char]) -> [(a, t)] -> [Char]
showMapList showValue xs = intercalate "\n" (map (\(k, v)-> show k ++ ":" ++ showValue v) xs) ++ "\n"

showEntity:: OpeMap -> Entity -> String
showEntity omap ent = "Type:" ++ showFom omap (entType ent) ++ ", FunAttr:" ++ show (entFunAttr ent)

showContext:: Context -> String
showContext con = showMapList (showEntity omap) (concatMap M.toList $ conEnt con)
    ++ showMapList (intercalate "\n" . map (showRule omap)) (M.toList $ conSimp con)
    ++ showMapList (intercalate "\n" . map (showRule omap)) (M.toList $ conImpl con)
    ++ show (conList con) where omap = conOpe con

showEmb:: EmbString -> [String] -> String
showEmb [EmbStr str] args = intercalate (str ++ " ") args
showEmb parts args = concatMap showPart parts where
    showPart:: EmbPart -> String
    showPart (EmbVar var) = args !! var
    showPart (EmbStr str) = str ++ " "

showLatex:: Fom -> Analyzer String
showLatex fom = fmap fst (showLatex fom) where
    showLatex:: Fom -> Analyzer (String, Operator)
    showLatex fun@FunFom{} = do
        omap <- fmap conOpe getContext
        let name = idStr $ funName fun
        let hostOpe = fromMaybe defaultOpe $ M.lookup name omap
        let bracket (str, ope) = if opePreceed hostOpe <= opePreceed ope then str else "\\left(" ++ str ++ "\\right)"
        mEnt <- lookupEnt name
        args <- mapM showLatex $ funArgs fun
        return $ (, hostOpe) $ case mEnt >>= entLatex of
            Nothing
                | isAlpha (head name)    -> name ++ "\\left(" ++ intercalate "," (map fst args) ++ "\\right)"
                | opeArgNum hostOpe == 1 -> name ++ bracket (head args)
                | otherwise              -> intercalate name $ map bracket args
            Just emb -> showEmb emb $ map bracket args
    showLatex fom = do
        omap <- fmap conOpe getContext
        return (showFom omap fom, Operator 2 100 True)

toJsonList:: [String] -> String
toJsonList xs = "[" ++ intercalate "," xs ++ "]"

instance ToJson Reason where
    toJson (NormalReason rule asg) = object [ "kind".= return "normal", "rule".= toJson rule, "asg".= toJsonMap asg ]
    toJson (UnfoldReason ent asg) = object [ "kind".= return "unfold", "asg".= toJsonMap asg ]
    toJson EqualReason = object [ "kind".= return "equal" ]
    toJson ACNormalizeReason = object [ "kind".= return "acnom" ]

instance ToJson Fom where
    toJson fom = object [
        "body".= showPart fom,
        "vars".= toJsonMap (varMap fom M.empty)]
        where
        varMap:: Fom -> AssignMap -> AssignMap
        varMap (VarFom id ty) = M.insert (idStr id) ty
        varMap fun@FunFom{} = mapF varMap (funArgs fun)where 
        varMap _ = id
        showPart:: Fom -> Analyzer String
        showPart (Rewrite res bf af) = object [
            "kind".= return "rewrite",
            "reason".= toJson res,
            "before".= showPart bf,
            "after".= showPart af]
        showPart fom = object [
            "kind".= return "normal",
            "tex".= showLatex fom]

instance ToJson Rule where
    toJson rule = object [
        "kind".= return (showRuleKind $ ruleKind rule),
        "label".= return (ruleLabel rule),
        "before".= toJson (ruleBf rule),
        "after".= toJson (ruleAf rule),
        "prop".= toJson (ruleProp rule)]
        where
        showRuleKind:: RuleKind -> String
        showRuleKind = \case SimpRule-> "simp"; ImplRule-> "impl"; EqualRule-> "equal"