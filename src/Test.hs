module Test where
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.State
import Parse
import Engine
import Type

tokenizeTest line = intercalate "," $ map show $ tokenize line
parserTest x = show . runState x . tokenize

simplifyTest:: String -> String -> String
simplifyTest prg str = ""
        -- ++ "simp:" ++ show simp ++ "\n"
        -- ++ "expr':" ++ show expr' ++ "\n"
        -- ++ "expr'':"  ++ show expr'' ++ "\n"
        -- ++ "expr:" ++ show expr ++ "\n" 
        ++ "simpList:" ++ show simpList ++ "\n"
        ++ "stepRule:" ++ show stepRule ++ "\n"
        ++ "implRule:" ++ show implRule ++ "\n"
        ++ "omap:" ++ show omap ++ "\n"
        ++ "tmap:" ++ show tmap ++ "\n"
        ++ "msgs:" ++ msg ++ "\n"
        ++ "out:" ++ out ++ "\n"
        ++ "out2:" ++ showExprAsRewrites simp ++ "\n"
        -- ++ "declas:" ++ show declas ++ "\n" 
        -- ++ "props:" ++ show declas ++ "\n"
        -- ++ "rules:" ++ show (makeRules props) ++ "\n" 
        where
    ((stepRule, implRule, simpList), omap, tmap, msgs) = buildProgram prg
    msg = intercalate "\n" $ fmap show msgs
    expr' = (evalState $ parseExpr omap) (tokenize str)
    expr'' = fromMaybe (error "wrong expr") expr'
    expr = appSimp simpList expr''
    simp = simplify stepRule expr
    steps = showSteps simp
    out = intercalate "\n=" steps
    out' = intercalate "\n=" steps

parseExprs str = fromMaybe [] $ evalState (parseCommaSeparated $ parseExpr M.empty) $ tokenize str

unifyTest:: String -> String
unifyTest str = out where
    exprs = parseExprs str
    [a, b] = exprs
    out = show $ unify a b

derivateTest:: String -> String -> String
derivateTest prg str = out' where
    ((stepRule, implRule, simpList), omap, tmap, msgs) = buildProgram prg
    exprs = parseExprs str
    [a, b] = exprs
    out = show $ derivate implRule (a, b)
    out' = out ++ "implRule:" ++ show implRule ++ "\n" ++ "stepRule:" ++ show stepRule ++ "\n" ++ "msgs:" ++ show msgs ++ "\n"

test x = forever $ getLine >>= (putStrLn . x)
testFunc2 = test $ parserTest $ parseDecla M.empty
testFunc = do
    file <- readFile "test.txt"
    test $ derivateTest file
testFunc4 = do
    file <- readFile "test.txt"
    test $ simplifyTest file
