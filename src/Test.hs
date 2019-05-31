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
import Rewriter

showMsgs msgs = intercalate "\n" $ map show msgs

toTokens:: String -> [PosToken]
toTokens str = toks where
    (msgs, pos, rest, toks) = runLexer tokenize (initialPosition, str)

tokenizeTest:: String -> String
tokenizeTest str = show toks ++ "\n" ++ showMsgs msgs where
    (msgs, pos, rest, toks) = runLexer tokenize (initialPosition, str)

parseExprTest:: String -> String
parseExprTest str = show $ parseExprs M.empty str

buildTest:: String -> String
buildTest str = showContext con ++ "\n" ++ showMsgs msgs where 
    (msgs, con) = buildProgram str

reasoningTest:: String -> String -> String
reasoningTest prg str = showContext con ++ "\n" ++ showMsgs (msgs ++ msgs') ++ "\n" ++ res where
    (msgs, con) = buildProgram prg
    (msgs', _, res) = analyze (reasoning str) con

reasoning:: String -> Analyzer String
reasoning str = do
    omap <- fmap conOpe getContext
    let exps = if null str then [] else parseExprs omap str
    foms <- mapM (buildFomEx AllowUndefined) exps
    case foms of
        [Just fom] -> do
            let fomStr = show fom
            res <- simplify fom
            let latStr = show $ latestFom res
            return $ fomStr ++ "\n" ++ latStr ++ "\n" ++ showFom omap res
        [Just a, Just b] -> do
            let fomStr = show a
            res <- derivate (a, b)
            return $ fomStr ++ "\n" ++ maybe "Nothing" (showFom omap) res
        _ -> return ""

test x = forever $ getLine >>= (putStrLn . x)
-- testFunc2 = test $ parserTest $ parseExpr M.empty

testFunc2 = do
    str <- getLine
    putStrLn $ buildTest str

testFunc = do
    file <- readFile "test.txt"
    str <- getLine
    putStrLn $ reasoningTest file str
    return ()
    -- test $ reasoningTest file
