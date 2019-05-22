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

tokenizeTest line = intercalate "," $ map show $ tokenize line
parserTest x = show . runState x . tokenize

showMessages msgs = intercalate "\n" $ map show msgs
parseExprs str = fromMaybe [] $ evalState (parseCommaSeparated $ parseExpr M.empty) $ tokenize str

showContext (Context tmap smap (rsmap, rimap)) = toJsonFormatedWith showExpr tmap ++ "\n"
    ++ toJsonFormatedWith (show " >>= ") rsmap ++ "\n"
    ++ toJsonFormatedWith (show " -> ") rimap 
    where
    show s x = "[" ++ intercalate ", " (map (showRule s) x) ++ "]"
    showRule s (a, b) = showExpr a ++ s ++ showExpr b

simplifyTest:: String -> String -> String
simplifyTest prg str = out ++ "\n" ++ showMessages msg ++ "\n" ++ showContext ctx where
    ((omap, ctx@(Context tmap smap (rsmap, rimap))), msg) = runWriter $ buildProgram prg
    (minput, rest) = (runState $ parseExpr omap) (tokenize str)
    out = case minput of
        Just input -> intercalate "" steps where
            expr = simplify smap rsmap input
            steps = showSteps expr
        Nothing -> "parse error"

unifyTest:: String -> String
unifyTest str = out where
    exprs = parseExprs str
    [a, b] = exprs
    out = show $ unify a b

derivateTest:: String -> String -> String
derivateTest prg str = out ++ "\n" ++ showMessages msg ++ "\n" ++ showContext ctx where
    ((omap, ctx@(Context tmap smap (rsmap, rimap))), msg) = runWriter $ buildProgram prg
    exprs = parseExprs str
    [a, b] = exprs
    out = intercalate "\n" steps where
        expr = derivate rimap (a, b)
        steps = maybe [] showSteps expr

test x = forever $ getLine >>= (putStrLn . x)
testFunc2 = test $ parserTest $ parseDecla M.empty
testFunc' = do
    file <- readFile "test.txt"
    test $ derivateTest file
testFunc = do
    file <- readFile "test.txt"
    test $ simplifyTest file
