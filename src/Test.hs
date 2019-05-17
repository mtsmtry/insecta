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
simplifyTest prg str = "out:" ++ out ++ "\n"
        -- ++ "out':" ++ out' ++ "\n"
        -- ++ "simp:" ++ show simp ++ "\n"
        -- ++ "expr':" ++ show expr' ++ "\n"
        -- ++ "expr'':"  ++ show expr'' ++ "\n"
        -- ++ "expr:" ++ show expr ++ "\n" 
        ++ "simpList:" ++ show simpList ++ "\n"
        ++ "stepRule:" ++ show stepRule ++ "\n"
        ++ "implRule:" ++ show implRule ++ "\n"
        ++ "omap:" ++ show omap ++ "\n"
        -- ++ "declas:" ++ show declas ++ "\n" 
        -- ++ "props:" ++ show declas ++ "\n"
        -- ++ "rules:" ++ show (makeRules props) ++ "\n" 
        where
    ((stepRule, implRule, simpList), omap, tmap) = buildProgram prg
    expr' = (evalState $ parseExpr omap) (tokenize str)
    expr'' = fromMaybe (error "wrong expr") expr'
    expr = appSimp simpList expr''
    simp = simplify stepRule expr
    steps = reverse $ showSteps simp
    out = intercalate "\n=" (map showExpr steps)
    out' = intercalate "\n=" (map show steps)

unifyTest:: String -> String
unifyTest str = out where
    exprs = fromMaybe [] $ evalState (parseCommaSeparated $ parseExpr M.empty) $ tokenize str
    [a, b] = exprs
    out = show $ unify a b

test x = forever $ getLine >>= (putStrLn . x)
-- testFunc = test $ parserTest parseVarDecs 
testFunc = do
    file <- readFile "test.txt"
    test $ simplifyTest file
