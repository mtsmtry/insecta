module Parse(someFunc) where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Map as M
import Control.Monad
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

getOpe = flip M.lookup $ M.fromList 
    [("+", (0, True)), ("-", (0, True)), ("*", (1, True)), ("/", (1, True)), ("^", (2, False))]

precederEq s ParenOpen = False
precederEq s (Ident _) = True
precederEq s (Symbol t) = precederEq' $ map getOpe' [s, t]
    where
        precederEq' [(aPre, aLeft), (bPre, bLeft)] = bLeft && ((aLeft && aPre <= bPre) || aPre < bPre)
        getOpe' = fromMaybe (0, True) . getOpe

data Operator = Operator Token Int
data Expr = IdentExpr String | FuncExpr Token [Expr] | StringExpr String | NumberExpr Int deriving (Show, Eq)

parseExpr:: State [Token] (Maybe Expr)
parseExpr = state $ \ts-> parseExpr ts [] [] where--4
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [Token] -> [(Token, Int)] -> [Expr] -> (Maybe Expr, [Token])
    parseExpr [] s q = (Just $ head $ makeExpr s q, [])
    parseExpr all@(x:xs) s q = case x of
        Error t m   -> (Nothing, all)
        Number n    -> maybeEnd $ parseExpr xs s (NumberExpr n:q)
        Ident i     -> maybeEnd $ if xs /= [] && head xs == ParenOpen
            then parseExpr xs ((x, 1):s) q
            else parseExpr xs s (IdentExpr i:q)
        ParenOpen   -> maybeEnd $ parseExpr xs ((x, 2):s) q -- 2 args for end condition
        ParenClose  -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            (opes, _:rest) = span ((/= ParenOpen) . fst) s
        Comma       -> parseExpr xs rest $ makeExpr opes q where
            isIdent x    = case x of Ident _ -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((/= ParenOpen) . fst) s
        Symbol ope  -> case getOpe ope of 
            Just _ -> parseExpr xs ((x, 2):rest) $ makeExpr opes q where
                (opes, rest) = span (precederEq ope . fst) s
            Nothing -> result 
        where
            result = (Just $ head $ makeExpr s q, all)
            maybeEnd a = if sum (map ((-1+) . snd) s) + 1 == length q then result else a
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(Token, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((t, n):os) q = makeExpr os $ FuncExpr t args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- Apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all

data VarDec = VarDec String Expr deriving (Show)
data VarDecSet = VarDecSet [String] Expr deriving (Show)
data Statement = StepStm Expr | ImplStm Expr | AssumeStm Expr [Statement] | BlockStm String Expr [Statement] deriving (Show)
data Proof = Proof [Statement] deriving (Show)
data Theorem = Theorem Expr Proof deriving (Show)

pand:: State [Token] (Maybe (a->b)) -> State [Token] (Maybe a) -> State [Token] (Maybe b)
pand f a = f >>= maybe (return Nothing) (\f'-> fmap f' <$> a)

expect:: State [Token] (Maybe a) -> State [Token] (Maybe b) -> State [Token] (Maybe a)
expect f a = f >>= maybe (return Nothing) (\f'-> maybe Nothing (const $ Just f') <$> a)

parseSequence:: State [Token] (Maybe a)-> State [Token] (Maybe [a])
parseSequence p = p >>= \case
    Just x' -> parseSequence p >>= \case
        Just s' -> return $ Just (x':s')
        Nothing -> return Nothing
    Nothing -> return $ Just []
    
parseToken:: Token -> State [Token] (Maybe Token) 
parseToken x = state $ \case
    [] -> (Nothing, [])
    all@(t:ts) -> if t == x then (Just x, ts) else (Nothing, all)

parseSymbol x = parseToken (Symbol x)
parseComma = parseToken Comma

parseIdent = state $ \case
    [] -> (Nothing, [])
    all@(t:ts) -> case t of Ident i-> (Just i, ts); _-> (Nothing, all)

parseSeparated:: State [Token] (Maybe s) -> State [Token] (Maybe a) -> State [Token] (Maybe [a]) 
parseSeparated s p = p >>= \case
    Just x' -> s >>= \case
        Just _ -> parseSeparated s p >>= \case
            Just r' -> return $ Just (x':r')
            Nothing -> return Nothing
        Nothing -> return $ Just [x']
    Nothing -> return $ Just []

parseCommaSeparated = parseSeparated parseComma

parseBlock = return (Just id) `expect` parseSymbol "{" `pand` parseSequence parseStatement `expect` parseSymbol "}"
parseVarDecSet = return (Just VarDecSet) `pand` parseCommaSeparated parseIdent `expect` parseSymbol ":" `pand` parseExpr
parseStatement = parseIdent >>= \case
    Just "step" -> return (Just StepStm) `pand` parseExpr
    Just "impl" -> return (Just ImplStm) `pand` parseExpr
    Just "assume" -> return (Just AssumeStm) `pand` parseExpr `pand` parseBlock
    _ -> return Nothing

parseVarDecs:: State [Token] (Maybe [(String, Expr)])
parseVarDecs = fmap conv (parseCommaSeparated parseVarDecSet) where
    toTuple (VarDecSet ns t) = (ns, repeat t)
    conv = Just . concatMap (uncurry zip) . maybe [] (map toTuple)

parseProof = parseSequence parseStatement

--parseTheorem = return (Just Theorim) `expect` 

unify:: Expr -> Expr -> State (M.Map String Expr) Bool 
unify (IdentExpr var) t = state $ \m-> maybe (True, M.insert var t m) (\x-> (x==t, m)) $ M.lookup var m
unify (NumberExpr n) (NumberExpr n') = return $ n == n'
unify (NumberExpr _) _ = return False
unify (FuncExpr f ax) (FuncExpr f' ax') = (and $ unify' ax ax') (f == f') where
    and f r = if r then f else return False
    unify' (e:ex) (e':ex') = unify e e' >>= and (unify' ex ex')
unify (FuncExpr _ _) _ = return False

assign:: M.Map String Expr -> Expr -> Expr
assign m e@(IdentExpr var) = fromMaybe e $ M.lookup var m
assign m (FuncExpr f args) = FuncExpr f $ map (assign m) args
assign m e = e

getTokenTest line = show token ++ ":" ++ rest where (token, rest) = getToken line
tokenizeTest line = intercalate "," $ map show $ tokenize line
parserTest x = show . runState x . tokenize

test x = forever $ getLine >>= (putStrLn . x)
someFunc = test $ parserTest $ parseCommaSeparated parseVarDecSet
