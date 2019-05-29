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

data RewriteList = RewriteFom Fom | RewriteList Reason Fom RewriteList

showRule:: OpeMap -> Rule -> String
showRule opem rule = showFom opem (ruleBf rule) ++ kind ++ showFom opem (ruleAf rule) where
    kind = case ruleKind rule of SimpRule -> " >>= "; ImplRule -> " => "

showReason:: OpeMap -> Reason -> String
showReason opem (NormalReason rule asg) = showRule opem rule ++ toJsonWith (showFom opem) asg
showReason opem EqualReason = ""

toRewriteList:: OpeMap -> Fom -> RewriteList
toRewriteList opem fun@FunFom{}  = build args [] where
    oldest (RewriteFom fom) = fom
    oldest (RewriteList _ _ rest) = oldest rest
    args = map (toRewriteList opem) (funArgs fun)
    build:: [RewriteList] -> [Fom] -> RewriteList
    build [] args = RewriteFom fun{funArgs=args}
    build (RewriteFom e:sargs) args = build sargs (e:args)
    build (RewriteList r old rest:sargs) args = RewriteList r fun{funArgs=(old:map oldest sargs ++ args)} (build (rest:sargs) args)
toRewriteList opem (Rewrite r a b) = add r blist alist where
    alist = toRewriteList opem a
    blist = toRewriteList opem b
    add:: Reason -> RewriteList -> RewriteList -> RewriteList
    add ar (RewriteList r e rest) trg = add ar rest $ RewriteList r e trg
    add ar (RewriteFom fom) trg = RewriteList ar fom trg
toRewriteList opem e = RewriteFom e

showRewriteList:: OpeMap -> RewriteList -> String
showRewriteList opem (RewriteFom e) = showOldestFom opem e
showRewriteList opem (RewriteList r e rest) = showOldestFom opem e
                                            ++ " [" ++ showReason opem r ++ "]" ++ "\n"
                                            ++ showRewriteList opem rest

showFunFom:: OpeMap -> (OpeMap -> Fom -> String) -> String -> [Fom]-> String
showFunFom opem fshow "tuple" as = "(" ++ intercalate ", " (map (fshow opem) as) ++ ")"
showFunFom opem fshow f args = if isAlpha (head f) 
    then f ++ "(" ++ intercalate ", " (map (fshow opem) args) ++ ")"
    else case args of
        [unary] -> f ++ fshow opem unary
        _ -> intercalate f (map (fshow opem) args)
    where
    getPre h = maybe 100 (\(_, x, _)-> x) $ M.lookup h opem
    bshow fun@FunFom{} = let g = idStr $ funName fun in if length (show g) == 2 && getPre f > getPre (show g) 
        then "(" ++ fshow opem fun ++ ")" 
        else fshow opem fun
    bshow fom = fshow opem fom

showFom:: OpeMap -> Fom -> String
showFom opem (StrFom id) = "\"" ++ idStr id ++ "\"" 
showFom opem (NumFom (IdentInt _ num)) = show num
showFom opem (VarFom id _) = idStr id
showFom opem (CstFom id _) = idStr id
showFom opem fun@FunFom{} = showFunFom opem showFom (idStr $ funName fun) (funArgs fun)
showFom opem rew@Rewrite{} = "[" ++ showFom opem (rewOlder rew) ++ ", " ++ showFom opem (rewLater rew) ++ "]"

showLatestFom opem rew@Rewrite{} = showLatestFom opem (rewLater rew)
showLatestFom opem fun@FunFom{} = showFunFom opem showLatestFom (idStr $ funName fun) (funArgs fun)
showLatestFom opem e = showFom opem e

showOldestFom opem rew@Rewrite{} = showOldestFom opem (rewOlder rew)
showOldestFom opem fun@FunFom{} = showFunFom opem showOldestFom (idStr $ funName fun) (funArgs fun)
showOldestFom opem e = showFom opem e

showFomAsRewrites:: OpeMap -> Fom -> String
showFomAsRewrites opem rew@Rewrite{} = "[" ++ intercalate ", " steps ++ "]" where
    steps = map (showFomAsRewrites opem) $ expandRewrite rew
    expandRewrite:: Fom -> [Fom]
    expandRewrite (Rewrite e a b) = expandRewrite b ++ expandRewrite a
    expandRewrite e = [e]
showFomAsRewrites opem fun@FunFom{} = showFunFom opem showFomAsRewrites (idStr $ funName fun) (funArgs fun)
showFomAsRewrites opem fom = showFom opem fom

evalString:: Expr -> String
evalString e = ""
