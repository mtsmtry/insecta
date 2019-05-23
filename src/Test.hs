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

lexer str = (\(_, _, _, x)-> x) $ runLexer tokenize (initialPosition, str)

tokenizeTest line = intercalate "," $ map show $ lexer line
parserTest x = show . runParser x . lexer

showMessages msgs = intercalate "\n" $ map show msgs
parseExprs str omap = (\(_, _, x)-> x) (runParser (parseCommaSeparated $ parseExpr omap) $ lexer str)

showContext (Context omap tmap smap (rsmap, rimap)) = toJsonFormatedWith (showExpr omap) tmap ++ "\n"
    ++ show omap ++ "\n"
    ++ toJsonFormatedWith (showr " >>= ") rsmap ++ "\n"
    ++ toJsonFormatedWith (showr " -> ") rimap ++ "\n"
    ++ show smap
    where
    showr s x = "[" ++ intercalate ", " (map (showRule s) x) ++ "]"
    showRule s (a, b) = showExpr omap a ++ s ++ showExpr omap b

reasoningTest:: String -> String -> String
reasoningTest prg str = showMessages msg ++ "\n" ++ showContext ctx ++ "\n" ++ out where
    (ctx@(Context omap tmap smap (rsmap, rimap)), msg) = runWriter $ buildProgram prg
    exprs = parseExprs str omap
    out = case exprs of
        [a, b] -> intercalate "\n" steps where
            expr = derivate rimap tmap (a, b)
            steps = maybe [] (showSteps omap) expr
        [input] -> intercalate "\n" steps where
            expr = simplify smap tmap rsmap input
            steps = showSteps omap expr
        _ -> "parse error"

unifyTest:: String -> String
unifyTest str = out where
    exprs = parseExprs str M.empty
    [a, b] = exprs
    out = show $ unify M.empty a b

test x = forever $ getLine >>= (putStrLn . x)
testFunc2 = test $ parserTest $ parseDecla M.empty
testFunc = do
    file <- readFile "test.txt"
    test $ reasoningTest file
