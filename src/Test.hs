module Test where
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Parser
import Library
import Analyzer
import Data
import Visualizer

showContext ctx = toJsonFormatedWith show (ctxScope ctx) ++ "\n"
    ++ show (ctxOMap ctx) ++ "\n"
    ++ toJsonFormatedWith (showr " >>= ") (ctxSRule ctx) ++ "\n"
    ++ toJsonFormatedWith (showr " => ") (ctxIRule ctx) ++ "\n"
    ++ show (ctxSimps ctx)
    where
    showr s x = "[" ++ intercalate ", " (map (showRule s) x) ++ "]"
    showRule s (a, b) = showExpr (ctxOMap ctx) a ++ s ++ showExpr (ctxOMap ctx) b

showMessages msgs = intercalate "\n" $ map show msgs

reasoningTest:: String -> String -> String
reasoningTest prg str = showMessages msg ++ "\n" ++ showContext ctx ++ "\n" ++ out where
    (msg, ctx) = buildProgram prg
    nexprs = parseExprs str (ctxOMap ctx)
    (_, _, exprs) = (analyze $ mapM typeExpr nexprs) ctx
    out = case exprs of
        [Just a, Just b] -> showRewriteList (ctxOMap ctx) (toRewriteList (ctxOMap ctx) expr) where
            mexpr = derivate (ctxIRule ctx) (a, b)
            expr = fromMaybe (NumberExpr NonePosition 0)  mexpr
        [Just input] -> showLatestExpr (ctxOMap ctx) expr ++ "\n" 
            ++ showExpr (ctxOMap ctx) expr ++ "\n" 
            ++ showExprAsRewrites (ctxOMap ctx) expr ++ "\n" 
            ++ showRewriteList (ctxOMap ctx) (toRewriteList (ctxOMap ctx) expr) where
            expr = simplify (ctxSRule ctx) input
        _ -> error $ show exprs

unifyTest:: String -> String
unifyTest str = out where
    exprs = parseExprs str M.empty
    [a, b] = exprs
    out = show $ unify a b

test x = forever $ getLine >>= (putStrLn . x)
-- testFunc2 = test $ parserTest $ parseExpr M.empty
testFunc = do
    file <- readFile "test.txt"
    test $ reasoningTest file
