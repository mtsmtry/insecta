module Type where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Writer
import Control.Arrow
import Control.Applicative
import Engine

type TypeMap = M.Map String Expr
type Message = Message String String

evalType:: TypeMap -> Expr -> Writer [] Expr
evalType tmap (IdentExpr i) = M.lookup i tmap
evalType tmap (FuncExpr )

analyzeDataType:: TypeMap -> Expr -> Bool
analyzeDataType t 

makeTypeMap:: [Decla] -> TypeMap
makeTypeMap [] = M.empty
makeTypeMap (x:xs) = getType (makeTypeMap xs) x where
    getType:: TypeMap -> Decla -> TypeMap
    getType m (Undef t e) = M.insert (showToken t) e m
    getType m (Define t args ret def) = M.insert (showToken t) item m where
        item = FuncExpr implies [FuncExpr tuple (map snd args), ret]
        tuple = PureExprHead $ Ident "tuple"
        implies = PureExprHead $ Symbol "->"
    getType m _ = m

buildProgram:: String -> ((RuleMap, RuleMap, Simplicity), OpeMap, TypeMap)
buildProgram str = (makeRuleMap props, omap, tmap) where
    ((declas, omap), rest) = runState parseProgram . tokenize $ str
    tmap = makeTypeMap declas
    props = extractMaybe $ map toProp declas
    toProp:: Decla -> Maybe Expr
    toProp (Axiom _ p) = Just p
    toProp (Theorem _ p _) = Just p
    toProp _ = Nothing