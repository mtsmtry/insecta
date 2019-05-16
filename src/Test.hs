module Test where
import Data.Char
import Data.List
import Data.Maybe
import Control.Monad.State
import Parse
import Engine

props = extractMaybe $maybe [] (map toProp) (fst declas)
(stepRule, implRule, simpList) = makeRuleMap props

tokenizeTest line = intercalate "," $ map show $ tokenize line
parserTest x = show . runState x . tokenize

simplifyTest:: String -> String
simplifyTest str = "result:" ++ show out ++ "\n"
        ++ "expr':" ++ show expr' ++ "\n"
        ++ "expr'':"  ++ show expr'' ++ "\n"
        ++ "expr:" ++ show expr ++ "\n" 
        ++ "simpList:" ++ show simpList ++ "\n"
        ++ "stepRule:" ++ show stepRule ++ "\n"
        ++ "implRule:" ++ show implRule ++ "\n"
        ++ "declas:" ++ show declas ++ "\n" 
        ++ "props:" ++ show declas ++ "\n"
        ++ "rules:" ++ show (makeRules props) ++ "\n" where
    expr' = evalState parseExpr (tokenize str)
    expr'' = fromMaybe (error "wrong expr") expr'
    expr = appSimp simpList expr''
    simp = simplify stepRule expr
    steps = showSteps simp
    out = intercalate "\n" (map show steps)

unifyTest:: String -> String
unifyTest str = out where
    exprs = fromMaybe [] $ evalState (parseCommaSeparated parseExpr) $ tokenize str
    [a, b] = exprs
    out = show $ unify a b

test x = forever $ getLine >>= (putStrLn . x)
-- testFunc = test $ parserTest parseVarDecs 
testFunc = test $ unifyTest
