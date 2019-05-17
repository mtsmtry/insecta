module Type where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Parse
import Engine

type TypeMap = M.Map String Expr
data Message = Message Position String String

evalType:: TypeMap -> Expr -> Writer [Message] (Maybe Expr)
evalType tmap (IdentExpr _ i) = return $ M.lookup i tmap
evalType tmap (FuncExpr (PureExprHead p h) as) = f $ \case
    FuncExpr (PureExprHead _ "implies") [FuncExpr (PureExprHead _ "tuple") ts, b]->
        checkArgs ts as >>= \x-> return (if x then ftype else Nothing)
    _-> writer (Nothing, [Message p h "is not function"]) 
    where
    checkArgs:: [Expr] -> [Expr] -> Writer [Message] Bool
    checkArgs [] [] = return True
    checkArgs [] _ = writer (False, [Message p h "wrong the number of arguments"])
    checkArgs _ [] = writer (False, [Message p h "wrong the number of arguments"])
    checkArgs (a:as) (t:ts) = (checkArgs as ts) where
        atype = evalType tmap a >>= return . maybe False (equals t)
    ftype = M.lookup h tmap
    f:: (Expr -> Writer [Message] (Maybe Expr)) -> Writer [Message] (Maybe Expr)
    f g = maybe (writer (Nothing, [Message p h "not defined"])) g ftype

makeTypeMap:: [Decla] -> TypeMap
makeTypeMap [] = M.empty
makeTypeMap (x:xs) = getType (makeTypeMap xs) x where
    getType:: TypeMap -> Decla -> TypeMap
    getType m (Undef t e) = M.insert (showToken t) e m
    getType m (Define t args ret def) = M.insert (showToken t) item m where
        item = FuncExpr (PureExprHead NonePosition "tuple") [FuncExpr (PureExprHead NonePosition "->") (map snd args), ret]
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