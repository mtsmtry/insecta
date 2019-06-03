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

showMessage:: Message -> String
showMessage (Message id msg) = showIdent id ++ ":" ++ msg where
    showPos (Position line column) = show line ++ " " ++ show column
    showIdent (Ident pos str) = "\"" ++ str ++ "\" (" ++ showPos pos ++ ")"

showMsgs msgs = intercalate "\n" $ map showMessage msgs

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
    foms <- subScope $ mapM (buildFomEx AllowUndefined) exps
    case foms of
        [Just fom] -> simplifyTest omap fom
        [Just a, Just b] -> do
            dev <- derivateTest omap a b
            meg <- mergeTest omap a b
            return $ dev ++ "\n\n" ++ meg
        _ -> return ""
    
simplifyTest:: OpeMap -> Fom -> Analyzer String
simplifyTest omap fom = do 
    let fomStr = show fom
    res <- simplify fom
    let latStr = show $ latestFom res
    return $ fomStr ++ "\n" ++ latStr ++ "\n" ++ showFom omap res

derivateTest:: OpeMap -> Fom -> Fom -> Analyzer String
derivateTest omap a b = do
    let fomStr = show a ++ "\n" ++ show b
    mRes <- derivate (a, b)
    return $ maybe "Nothing" (\res-> fomStr ++ "\n" ++ showFom omap res) mRes

mergeTest:: OpeMap -> Fom -> Fom -> Analyzer String
mergeTest omap a b = do
    simpA <- simplify a
    simpB <- simplify b
    let merge = mergeRewrite simpA simpB
    return $ "A:" ++ showFom omap simpA 
        ++ "\nB:" ++ showFom omap simpB 
        ++ "\nMerge:" ++ maybe "Nothing" (showFom omap) merge

test x = forever $ getLine >>= (putStrLn . x)
-- testFunc2 = test $ parserTest $ parseExpr M.empty

testFunc2 = do
    str <- getLine
    putStrLn $ buildTest str

testFunc = do
    file <- readFile "test.txt"
    putStrLn $ reasoningTest file ""
    forever $ do
        file <- readFile "test.txt"
        str <- getLine
        putStrLn $ reasoningTest file str
    return ()
    -- test $ reasoningTest file
