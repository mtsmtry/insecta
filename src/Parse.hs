module Parse(someFunc) where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Map as M
--import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow

data Token = EndLine | Ident String | Number Int 
    | Literal String | LiteralOne Char | Symbol String 
    | Comma | ParenOpen | ParenClose | Error String String deriving (Eq, Show)

getToken :: String -> (Maybe Token, String)
getToken [] = (Nothing, [])
getToken (x:xs)
    | isDigit x = make (Number . read) isDigit
    | isIdentHead x = make Ident isIdentBody
    | isOperator x = make Symbol isOperator
    | isBracket x = (Just $ toSymbol [x], xs)
    | x == '"' = make' Literal ('"' /=)
    | x == '#' = first (const Nothing) $ span ('\n' /=) xs
    | x == '\'' = make' toChar ('\'' /=)
    | isSpace x = (Nothing, xs)
    | otherwise = (Just $ Error [x] "wrong", xs)
    where
        make f g = first (Just . f . (x:)) $ span g xs
        make' f g = fmap (drop 1) $ first h $ span g xs
            where h all = Just $ case all of [] -> Error all "no"; _ -> f all
        [isIdentSymbol, isOperator, isBracket] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$:~`.", "(){}[],"]
        [isIdentHead, isIdentBody] = map any [[isLetter, ('_' ==)], [isLetter, isDigit, isIdentSymbol]]
            where any = F.foldr ((<*>) . (<$>) (||)) $ const False
        toChar all = case all of [x] -> LiteralOne x; [] -> Error all "too short"; (x:xs) -> Error all "too long"
        toSymbol all = case all of "(" -> ParenOpen; ")" -> ParenClose; "," -> Comma; _ -> Symbol all

tokenize :: String -> [Token]
tokenize [] = []
tokenize all = (\(x, xs)-> maybe xs (:xs) x) $ tokenize <$> getToken all

--newtype ParseState = ([Token], [Token])

precederEq s ParenOpen = False
precederEq s (Ident _) = True
precederEq s (Symbol t) = precederEq' $ map getOpe [s, t]
    where
        precederEq' [(aPre, aLeft), (bPre, bLeft)] = bLeft && ((aLeft && aPre <= bPre) || aPre < bPre)
        getOpe' = flip M.lookup $ M.fromList 
            [("+", (0, True)), ("-", (0, True)), ("*", (1, True)), ("/", (1, True)), ("^", (2, False))]
        getOpe = fromMaybe (0, True) . getOpe'

data Operator = Operator Token Int
data Expr = IdentExpr String | FuncExpr Token [Expr] | StringExpr String | NumberExpr Int deriving (Show, Eq)

parseExpr2:: State [Token] Expr
parseExpr2 = parseExpr [] [] where--4
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [(Token, Int)] -> [Expr] -> State [Token] Expr
    --parseExpr [] s q = (head $ makeExpr s q, [])
    parseExpr s q = state $ \all@(x:xs)-> case x of --all@(x:xs)
        Error t m   -> error "Illegal tokens"
        Number n    -> maybeEnd all $ nextParse s (NumberExpr n:q) xs
        Ident i     -> maybeEnd all $ if xs /= [] && head xs == ParenOpen
            then runState (parseExpr ((x, 1):s) q) xs
            else nextParse s (IdentExpr i:q) xs
        ParenOpen   -> maybeEnd $ nextParse ((x, 2):s) q xs -- 2 args for end condition
        ParenClose  -> maybeEnd all $ nextParse rest (makeExpr opes q) xs where
            (opes, _:rest) = span ((/= ParenOpen) . fst) s
        Comma       -> nextParse rest (makeExpr opes q) xs where
            isIdent x    = case x of Ident _ -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((/= ParenOpen) . fst) s
        Symbol ope  -> nextParse ((x, 2):rest) (makeExpr opes q) xs where
            (opes, rest) = span (precederEq ope . fst) s
        where
            nextParse s q = runState (parseExpr s q)
            maybeEnd all a = if sum (map ((-1+) . snd) s) + 1 == length q then (head $ makeExpr s q, all) else a
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(Token, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((t, n):os) q = makeExpr os $ FuncExpr t args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- Apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all

--parseVarDec:: [Token] -> [Token]
--parseVarDec x:xs =

unify:: Expr -> Expr -> State (M.Map String Expr) Bool 
unify (IdentExpr var) t = state $ \m-> maybe (True, M.insert var t m) (\x-> (x==t, m)) $ M.lookup var m
unify (NumberExpr n) (NumberExpr n') = return $ n == n'
unify (NumberExpr _) _ = return False
unify (FuncExpr f ax) (FuncExpr f' ax') = (and $ unify' ax ax') (f == f') where
    and f r = if r then f else return False
    unify' (e:ex) (e':ex') = unify e e' >>= and (unify' ex ex')
unify (FuncExpr _ _) _ = return False

getTokenTest line = show token ++ ":" ++ rest where (token, rest) = getToken line
tokenizeTest line = intercalate "," $ map show $ tokenize line
transformTest = (\(a, b)->show a ++ " : " ++ show b) . parseExpr . tokenize

test x = forever $ getLine >>= (putStrLn . x)
someFunc = test transformTest
