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
import Rewriter

data RewriteList = RewriteExpr Expr | RewriteList Reason Expr RewriteList

showReason:: OpeMap -> Reason -> String
showReason omap (StepReason (a, b) asg) = showExpr omap a ++ " >>= " ++ showExpr omap b ++ " " ++ toJsonWith (showExpr omap) asg
showReason omap (ImplReason (a, b) asg) = showExpr omap a ++ " -> " ++ showExpr omap b ++ " " ++ toJsonWith (showExpr omap) asg
showReason omap EqualReason = ""

toRewriteList:: OpeMap -> Expr -> RewriteList
toRewriteList omap (FuncExpr f as) = build args [] where
    oldest (RewriteExpr e) = e
    oldest (RewriteList _ _ rest) = oldest rest
    args = map (toRewriteList omap) as
    build:: [RewriteList] -> [Expr] -> RewriteList
    build [] args = RewriteExpr $ FuncExpr f args
    build (RewriteExpr e:sargs) args = build sargs (e:args)
    build (RewriteList r old rest:sargs) args = RewriteList r (FuncExpr f (old:map oldest sargs ++ args)) (build (rest:sargs) args)
toRewriteList omap (Rewrite r a b) = add r blist alist where
    alist = toRewriteList omap a
    blist = toRewriteList omap b
    add:: Reason -> RewriteList -> RewriteList -> RewriteList
    add ar (RewriteList r e rest) trg = add ar rest $ RewriteList r e trg
    add ar (RewriteExpr e) trg = RewriteList ar e trg
toRewriteList omap e = RewriteExpr e

showRewriteList:: OpeMap -> RewriteList -> String
showRewriteList omap (RewriteExpr e) = showOldestExpr omap e
showRewriteList omap (RewriteList r e rest) = showOldestExpr omap e
                                            ++ " [" ++ showReason omap r ++ "]" ++ "\n"
                                            ++ showRewriteList omap rest

showFuncExpr:: OpeMap -> (OpeMap -> Expr -> String) -> PosStr -> [Expr]-> String
showFuncExpr omap fshow (_, "tuple") as = "(" ++ intercalate ", " (map (fshow omap) as) ++ ")"
showFuncExpr omap fshow (_, f) as
    | not (isAlpha (head f)) && length as == 2 = let [a, b] = as; (former, latter) = (bshow a, bshow b) in case b of 
        (FuncExpr (_, g) _)-> if isAlpha (head g) then former ++ f ++ latter else former ++ f ++ "(" ++ latter ++ ")"
        _ -> former ++ f ++ latter
    | not (isAlpha (head f)) && length as == 1 = let arg = bshow (head as) in case head as of
        e@(FuncExpr (_, g) _) -> if isAlpha (head g) || head g == '(' then f ++ arg else f ++ "(" ++ arg ++ ")"
        _ -> f ++ arg
    | otherwise = f ++ "(" ++ intercalate ", " (map (fshow omap) as) ++ ")" where
        getPre h = maybe 100 (\(_, x, _)-> x) $ M.lookup h omap
        bshow e@(FuncExpr (_, g) as) = if length g == 2 && getPre f > getPre g then "(" ++ fshow omap e ++ ")" else fshow omap e
        bshow e = fshow omap e

showExpr:: OpeMap -> Expr -> String
showExpr omap (Rewrite _ a b) = "[" ++ showExpr omap a ++ ", " ++ showExpr omap b ++ "]"  -- error "Can not use Rewrite"
showExpr omap (StringExpr (_, s)) = "\"" ++ s ++ "\"" 
showExpr omap (IdentExpr (_, x)) = x
showExpr omap (NumberExpr _ n) = show n
showExpr omap (FuncExpr f as) = showFuncExpr omap showExpr f as

showLatestExpr omap (Rewrite _ a _) = showLatestExpr omap a
showLatestExpr omap (FuncExpr f as) = showFuncExpr omap showLatestExpr f as
showLatestExpr omap e = showExpr omap e

showOldestExpr omap (Rewrite _ _ b) = showLatestExpr omap b
showOldestExpr omap (FuncExpr f as) = showFuncExpr omap showOldestExpr f as
showOldestExpr omap e = showExpr omap e

showCodeExpr:: OpeMap -> Expr -> PosStr
showCodeExpr omap e = (getExprPos e, showOldestExpr omap e)

showExprAsRewrites:: OpeMap -> Expr -> String
showExprAsRewrites omap e@Rewrite{} = "[" ++ intercalate ", " steps ++ "]" where
    steps = map (showExprAsRewrites omap) $ expandRewrite e
    expandRewrite:: Expr -> [Expr]
    expandRewrite (Rewrite e a b) = expandRewrite b ++ expandRewrite a
    expandRewrite e = [e]
showExprAsRewrites omap (FuncExpr h as) = showFuncExpr omap showExprAsRewrites h as
showExprAsRewrites omap e = showExpr omap e

evalString:: Expr -> String
evalString e = ""
