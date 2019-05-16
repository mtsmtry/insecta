module Parse where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative

data Token = EndLine | Ident String | Number Int 
    | Literal String | LiteralOne Char | Symbol String 
    | Comma | ParenOpen | ParenClose | Error String String deriving (Eq, Show)
tokenize :: String -> [Token]
tokenize [] = []
tokenize all = (\(x, xs)-> maybe xs (:xs) x) $ tokenize <$> getToken all where
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
            -- (token constructor, tail condition) -> (token, rest string)
            make f g = first (Just . f . (x:)) $ span g xs
            make' f g = fmap (drop 1) $ first h $ span g xs
                where h all = Just $ case all of [] -> Error all "no"; _ -> f all
            -- Char -> Bool
            [isIdentSymbol, isOperator, isBracket] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$:~`.", "(){}[],"]
            [isIdentHead, isIdentBody] = map any [[isLetter, ('_' ==)], [isLetter, isDigit, isIdentSymbol]]
                where any = F.foldr ((<*>) . (<$>) (||)) $ const False
            -- String -> Token
            toChar all = case all of [x] -> LiteralOne x; [] -> Error all "too short"; (x:xs) -> Error all "too long"
            toSymbol all = case all of "(" -> ParenOpen; ")" -> ParenClose; "," -> Comma; _ -> Symbol all

type Rule = (Expr, Expr)
data ExprHead = ExprHead Token Int | PureExprHead Token deriving (Show, Eq)
data Expr = IdentExpr String | FuncExpr ExprHead [Expr] | StringExpr String | NumberExpr Int | Rewrite Rule Expr Expr deriving (Show, Eq)
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
        Comma       -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            isIdent x    = case x of Ident _ -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((/= ParenOpen) . fst) s
        Symbol ope  -> case getOpe ope of 
            Just _      -> parseExpr xs ((x, 2):rest) $ makeExpr opes q where
                (opes, rest) = span (precederEq ope . fst) s
            Nothing     -> result 
        where
            result = (Just $ head $ makeExpr s q, all)
            maybeEnd a = if sum (map ((-1+) . snd) s) + 1 == length q then result else a
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(Token, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((t, n):os) q = makeExpr os $ FuncExpr (PureExprHead t) args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all
    -- String -> (preceed, left associative)
    getOpe = flip M.lookup $ M.fromList 
        [(">>=", (0, True)), ("->", (1, True)), ("+", (10, True)), ("-", (10, True)), ("*", (11, True)), ("/", (11, True)), ("^", (12, False))]
    precederEq:: String -> Token -> Bool
    precederEq s ParenOpen = False
    precederEq s (Ident _) = True
    precederEq s (Symbol t) = precederEq' $ map getOpe' [s, t] where
        precederEq' [(aPre, aLeft), (bPre, bLeft)] = bLeft && ((aLeft && aPre <= bPre) || aPre < bPre)
        getOpe' = fromMaybe (0, True) . getOpe

infixl 1 <++>
(<++>):: State [Token] (Maybe (a->b)) -> State [Token] (Maybe a) -> State [Token] (Maybe b)
f <++> a = f >>= maybe (return Nothing) (\f'-> fmap f' <$> a)

infixl 1 <::>
(<::>):: State [Token] (Maybe a) -> State [Token] (Maybe b) -> State [Token] (Maybe a)
f <::> a = f >>= maybe (return Nothing) (\f'-> maybe Nothing (const $ Just f') <$> a)

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
parseCommaSeparated = parseSeparated $ parseToken Comma

data VarDecSet = VarDecSet [String] Expr deriving (Show)
parseVarDecSet:: State [Token] (Maybe VarDecSet)
parseVarDecSet = return (Just VarDecSet) <++> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr

data Statement = StepStm Expr | ImplStm Expr | AssumeStm Expr [Statement] | BlockStm String Expr [Statement] deriving (Show)
parseStatement:: State [Token] (Maybe Statement)
parseStatement = parseIdent >>= \case
    Just "step" -> return (Just StepStm) <++> parseExpr
    Just "impl" -> return (Just ImplStm) <++> parseExpr
    Just "assume" -> return (Just AssumeStm) <++> parseExpr <++> parseBlock
    _ -> return Nothing 
    where parseBlock = return (Just id) <::> parseSymbol "{" <++> parseSequence parseStatement <::> parseSymbol "}"

type VarDec = [(String, Expr)]
parseVarDecs:: State [Token] (Maybe VarDec)
parseVarDecs = fmap conv (parseCommaSeparated parseVarDecSet) where
    toTuple (VarDecSet ns t) = (ns, repeat t)
    conv = Just . concatMap (uncurry zip) . maybe [] (map toTuple)
parseParenVarDecs = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs <::> parseToken ParenClose

data Decla = Axiom VarDec Expr | Theorem VarDec Expr [Statement] 
    | Define String VarDec Expr | Predicate String String Expr VarDec Expr deriving (Show)
parseDecla:: Maybe String -> State [Token] (Maybe Decla)
parseDecla (Just "axiom") = return (Just Axiom)
    <++> parseParenVarDecs 
    <::> parseSymbol "{" <++> parseExpr <::> parseSymbol "}"
parseDecla (Just "theorem") = return (Just Theorem) 
    <++> parseParenVarDecs 
    <::> parseSymbol "{" 
    <++> parseExpr 
    <::> parseToken (Ident "proof") <::> parseSymbol ":" <++> parseSequence parseStatement
    <::> parseSymbol "}"
parseDecla (Just "define") = return (Just Define)
    <++> parseIdent
    <++> parseParenVarDecs 
    <::> parseSymbol "{" <++> parseExpr <::> parseSymbol "}"
parseDecla (Just "predicate") = return (Just Predicate)
    <++> parseIdent
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr <::> parseSymbol "]"
    <++> parseParenVarDecs
    <::> parseSymbol "{" <++> parseExpr <::> parseSymbol "}"
parseDecla _ = return Nothing

parseProgram:: State [Token] (Maybe [Decla])
parseProgram = parseSequence $ parseIdent >>= parseDecla