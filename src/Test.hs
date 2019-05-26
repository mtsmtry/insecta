module Test where
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Parser
import Library
import Rewriter
import Analyzer
import Data
import Visualizer

lexer str = (\(_, _, _, x)-> x) $ runLexer tokenize (initialPosition, str)
parser p t = (\(_, _, x)-> x) $ runParser p t

tokenizeTest line = intercalate "," $ map show $ lexer line
parserTest x = show . parser x . lexer

showMessages msgs = intercalate "\n" $ map show msgs
parseExprs str omap = (\(_, _, x)-> x) (runParser (parseCommaSeparated $ parseExpr omap) $ lexer str)

showContext ctx = toJsonFormatedWith (showExpr (ctxOMap ctx)) (ctxTMap ctx) ++ "\n"
    ++ show (ctxOMap ctx) ++ "\n"
    ++ toJsonFormatedWith (showr " >>= ") (ctxSRule ctx) ++ "\n"
    ++ toJsonFormatedWith (showr " => ") (ctxIRule ctx) ++ "\n"
    ++ show (ctxSimps ctx)
    where
    showr s x = "[" ++ intercalate ", " (map (showRule s) x) ++ "]"
    showRule s (a, b) = showExpr (ctxOMap ctx) a ++ s ++ showExpr (ctxOMap ctx) b

reasoningTest:: String -> String -> String
reasoningTest prg str = showMessages msg ++ "\n" ++ showContext ctx ++ "\n" ++ out where
    (msg, ctx) = buildProgram prg
    exprs = parseExprs str (ctxOMap ctx)
    out = case exprs of
        [a, b] -> showRewriteList (ctxOMap ctx) (toRewriteList (ctxOMap ctx) expr) where
            mexpr = derivate (ctxIRule ctx) (a, b)
            expr = fromMaybe (NumberExpr NonePosition 0)  mexpr
        [input] -> showLatestExpr (ctxOMap ctx) expr ++ "\n" 
            ++ showExpr (ctxOMap ctx) expr ++ "\n" 
            ++ showExprAsRewrites (ctxOMap ctx) expr ++ "\n" 
            ++ showRewriteList (ctxOMap ctx) (toRewriteList (ctxOMap ctx) expr) where
            expr = simplify (ctxSRule ctx) input
        _ -> "parse error"

unifyTest:: String -> String
unifyTest str = out where
    exprs = parseExprs str M.empty
    [a, b] = exprs
    out = show $ unify a b

test x = forever $ getLine >>= (putStrLn . x)
testFunc2 = test $ parserTest $ parseExpr M.empty
testFunc = do
    file <- readFile "test.txt"
    test $ reasoningTest file
