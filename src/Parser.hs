module Parser where
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
import Control.Applicative
import Library

newtype Parser a = Parser { runParser::[PosToken] -> ([Message], [PosToken], a) }

instance Functor Parser where
    fmap f (Parser g) = Parser $ \ts -> let (m, ts', x) = g ts in (m, ts', f x)

instance Applicative Parser where
    pure = return
    a <*> b = do
        f <- a
        f <$> b

instance Monad Parser where
    return x = Parser ([], , x)
    (Parser h) >>= f = Parser $ \ts ->
        let (m, ts', x) = h ts
            (Parser g) = f x
            (m', ts'', x') = g ts'
        in  (m ++ m', ts'', x')

-- Position(Line, Char)
data Position = Position Int Int | NonePosition deriving (Show)

initialPosition = Position 1 1
addChar (Position l c) n = Position l (c+n)
nextChar (Position l c) = Position l (c+1)
nextLine (Position l c) = Position (l+1) 1

-- Labeled string
data Token = Ident String | Number Int 
    | Literal String | LiteralOne Char | Symbol String | Operator String
    | Comma | ParenOpen | ParenClose | Error String String deriving (Eq, Show)

showToken:: Token -> String
showToken (Symbol s) = s
showToken (Operator s) = s
showToken (Ident s) = s
showToken (Number n) = show n
showToken (Literal s) = '"':s ++ "\""
showToken (LiteralOne s) = ['\'', s, '\'']
showToken Comma = ","
showToken ParenOpen = "("
showToken ParenClose = ")"
showToken (Error s _) = s

-- Token with Position
data PosToken = PosToken Position Token deriving (Show)

type PosStr = (Position, String)

sameStr (_, a) (_, b) = a == b

makePosStr:: String -> PosStr
makePosStr s = (NonePosition, s)

data Message = Message PosStr String deriving (Show)

-- Pop token from string 
-- (current position, input string) -> (poped token, rest string, new position)
popToken:: Position -> String -> (Maybe PosToken, String, Position)
popToken p [] = (Nothing, [], p)
popToken p (x:xs)
    | isDigit x = make (Number . read) isDigit
    | isIdentHead x = make Ident isIdentBody
    | isOperator x = make Operator isOperator
    | isSymbol x = (Just $ PosToken p $ toSymbol [x], xs, nextChar p)
    | x == '"' = make' Literal ('"' /=)
    | x == '#' = let (t, rest) = span ('\n' /=) xs in (Nothing, rest, addChar p $ length t) 
    | x == '\'' = make' toChar ('\'' /=)
    | x == '\n' = (Nothing, xs, nextLine p)
    | isSpace x = (Nothing, xs, nextChar p)
    | otherwise = (Just $ PosToken p $ Error [x] "wrong", xs, nextChar p) 
    where
    appPos:: Token -> PosToken
    appPos = PosToken p
    -- (token constructor, tail condition) -> (token, rest string, position)
    make f g = ((Just . appPos . f . (x:)) t, rest, addChar p $ length t) where (t, rest) = span g xs
    make' f g = (appPos <$> (h t), drop 1 rest, addChar p $ length t) where 
        (t, rest) = span g xs
        h all = Just $ case all of [] -> Error all "no"; _ -> f all
    -- Char -> Bool
    [isIdentSymbol, isOperator, isSymbol] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$~`.&%", "(){}[],:"]
    [isIdentHead, isIdentBody] = map any [[isLetter, ('_' ==)], [isLetter, isDigit, isIdentSymbol]]
        where any = F.foldr ((<*>) . (<$>) (||)) $ const False
    -- String -> Token
    toChar all = case all of [x] -> LiteralOne x; [] -> Error all "too short"; (x:xs) -> Error all "too long"
    toSymbol all = case all of "(" -> ParenOpen; ")" -> ParenClose; "," -> Comma; _ -> Symbol all

-- string to tokens
tokenize:: String -> [PosToken]
tokenize = tokenize' initialPosition where
    tokenize' :: Position -> String -> [PosToken]
    tokenize' p [] = []
    tokenize' p all = let (x, xs, p') = popToken p all in maybe id (:) x (tokenize' p' xs)

-- Term rewriting rule
-- (before expression, after expression)
type Rule = (Expr, Expr)

-- Operator map
-- M.Map(operator string, (preceed, is left associative))
-- preceeder as high value (ex = 1, + 2)
type OpeMap = M.Map String (Int, Int, Bool)

type AssignMap = M.Map String Expr
data Reason = StepReason Rule AssignMap | ImplReason Rule AssignMap | EqualReason deriving (Show)

-- Expression
-- has position on code
data Expr = IdentExpr PosStr | FuncExpr PosStr [Expr] 
        | StringExpr PosStr | NumberExpr Position Int | Rewrite Reason Expr Expr deriving (Show)

makeIdentExpr:: String -> Expr
makeIdentExpr = IdentExpr . makePosStr

getPosAndStr:: Expr -> PosStr
getPosAndStr (IdentExpr ps) = ps
getPosAndStr (StringExpr ps) = ps
getPosAndStr (NumberExpr p n) = (p, show n)
getPosAndStr (Rewrite _ a _) = getPosAndStr a
getPosAndStr (FuncExpr ps _) = ps

-- parse expression by shunting yard algorithm
parseExpr:: OpeMap -> Parser (Maybe Expr)
parseExpr omap = Parser $ \ts-> parseExpr ts [] [] where
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [PosToken] -> [(PosToken, Int)] -> [Expr] -> ([Message], [PosToken], Maybe Expr)
    parseExpr [] s q = ([], [], Just $ head $ makeExpr s q)
    parseExpr all@(px@(PosToken p x):xs) s q = case x of
        Error t m   -> ([], all, Nothing)
        Number n    -> maybeEnd $ parseExpr xs s (NumberExpr p n:q)
        Ident i     -> maybeEnd $ case xs of
            (po@(PosToken _ ParenOpen):xs')-> parseExpr xs' ((po, 2):(px, 1):s) q
            _-> parseExpr xs s (IdentExpr (p, i):q)
        ParenOpen   -> maybeEnd $ parseExpr xs ((px, 2):(tuple, 1):s) q -- 2 args for end condition
        ParenClose  -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            (opes, _:rest) = span ((not <$> isParenOpen) . fst) s
        Comma       -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            isIdent = \case PosToken _ (Ident _) -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((not <$> isParenOpen) . fst) s
        Operator ope -> parseExpr xs ((px, narg):rest) $ makeExpr opes q where
            (msg, (narg, preceed, lassoc)) = getOpe (p, ope)
            (opes, rest) = span (precederEq (preceed, lassoc) . fst) s
        Symbol{} -> result
        where
            isParenOpen = \case PosToken _ ParenOpen -> True; _ -> False
            result = ([], all, Just $ head $ makeExpr s q)
            maybeEnd a = if sum (map ((-1+) . snd) s) + 1 == length q then result else a
    tuple = PosToken NonePosition (Ident "tuple")
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(PosToken, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((PosToken _ (Ident "tuple"), 1):os) q = makeExpr os q
    makeExpr ((PosToken p t, n):os) q = makeExpr os $ FuncExpr (p, showToken t) args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all
    -- String -> (preceed, left associative)
    defaultOpe = (-1, 2, True)
    getOpe:: PosStr -> ([Message], (Int, Int, Bool))
    getOpe x@(p, s) = maybe ([Message x "Not defined infix"], defaultOpe) ([], ) (M.lookup s omap)
    precederEq:: (Int, Bool) -> PosToken -> Bool
    precederEq _ (PosToken _ ParenOpen) = False
    precederEq _ (PosToken _ (Ident _)) = True
    precederEq (apre, aleft) (PosToken _ (Operator t)) = aleft && ((bleft && apre <= bpre) || apre < bpre)
        where (_, bpre, bleft) = fromMaybe defaultOpe $ M.lookup t omap

-- atom parsers
parseToken:: Token -> Parser (Maybe Token)
parseToken x = Parser $ \case
    [] -> ([], [], Nothing)
    all@((PosToken _ t):ts) -> if t == x then ([], ts, Just x) else ([], all, Nothing)
parseSymbol x = parseToken (Symbol x)
parseOperator x = parseToken (Operator x)

parseAnyOperator:: Parser (Maybe PosStr)
parseAnyOperator = Parser $ \case
    [] -> ([], [], Nothing)
    (PosToken p (Operator s):ts) -> ([], ts, Just (p, s))
    all -> ([], all, Nothing)

parseNumber:: Parser (Maybe Int)
parseNumber = Parser $ \case
    [] -> ([], [], Nothing)
    all@((PosToken _ t):ts) -> case t of Number n-> ([], ts, Just n); _-> ([], all, Nothing)

parseIdent:: Parser (Maybe PosStr)
parseIdent = Parser $ \case
    [] -> ([], [], Nothing)
    (PosToken _ (Ident "operator"):PosToken p (Operator s):ts) -> ([], ts, Just (p, s))
    (PosToken p (Ident s):ts) -> ([], ts, Just (p, s))
    all -> ([], all, Nothing)

parseSeparated:: Parser (Maybe s) -> Parser (Maybe a) -> Parser [a]
parseSeparated s p = p >>= \case
    Just x' -> s >>= \case
        Just _ -> parseSeparated s p >>= \r' -> return (x':r')
        Nothing -> return [x']
    Nothing -> return []

-- parser connecters
infixl 1 <++>
(<++>):: Parser (Maybe (a->b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <++> latter = former >>= \case
    Just f -> latter >>= \case
            Just x -> return $ Just (f x)
            Nothing -> return Nothing
    Nothing -> return Nothing

infixl 1 <&&>
(<&&>):: Parser (Maybe (a->b)) -> Parser a -> Parser (Maybe b)
former <&&> latter = former >>= \case
    Just f -> latter >>= return . Just . f
    Nothing -> return Nothing

infixl 1 <::>
(<::>):: Parser (Maybe a) -> Parser (Maybe b) -> Parser (Maybe a)
former <::> latter = former >>= \case
    Just f -> latter >>= \case
            Just x -> return $ Just f
            Nothing -> return Nothing
    Nothing -> return Nothing

parseSequence:: Parser (Maybe a) -> Parser [a]
parseSequence p = p >>= \case
    Just x' -> parseSequence p >>= return . (x':)
    Nothing -> return $ []

parseCommaSeparated:: Parser (Maybe a) -> Parser [a]
parseCommaSeparated = parseSeparated $ parseToken Comma

-- parser parts
data VarDecSet = VarDecSet [PosStr] Expr deriving (Show)
parseVarDecSet:: OpeMap -> Parser (Maybe VarDecSet)
parseVarDecSet omap = return (Just VarDecSet) <&&> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr omap

-- [proof] = [command] [expr] [command] [expr]

-- [proof]
-- [command] assume [expr] {
--     being [expr]
--     [multi-proof]
-- }

-- [proof]
-- fork [proof]
-- fork [proof]


-- return x >>= f  == f x
-- m >>= return    == m
-- (m >>= f) >>= g == m >>= (\x -> f x >>= g)

    
data Command = StepCmd | ImplCmd | WrongCmd String deriving (Show)
data Statement = SingleStm Command Expr
    | BlockStm [Statement]
    | AssumeStm Command Expr Expr Statement
    | ForkStm [Statement] deriving (Show)

makeParser f = return $ Just ([], f)

parseMultiLineStm:: OpeMap -> Parser (Maybe Statement)
parseMultiLineStm omap = return (Just BlockStm) <&&> parseSequence (parseStatement omap)

parseStatement:: OpeMap -> Parser (Maybe Statement)
parseStatement omap = parseSymbol "{" >>= \case 
    Just{} -> parseBlock
    Nothing -> parseSingleStm
    where
    parseCmd = parseIdent >>= \case
        Just (_, "step") -> return $ Just StepCmd
        Just (_, "impl") -> return $ Just ImplCmd
        Just (_, s) -> return $ Just $ WrongCmd s
    parseBlock = return (Just BlockStm) <&&> parseSequence (parseStatement omap) <::> parseSymbol "}"
    parseSingleStm = parseCmd >>= \case
        Just cmd -> parseIdent >>= \case
            Just (_, "assume") -> return (Just $ AssumeStm cmd)
                <++> parseExpr omap <::> parseSymbol "{"
                <::> parseToken (Ident "begin") <++> parseExpr omap 
                <++> parseMultiLineStm omap <::> parseSymbol "}"
            _ -> return (Just $ SingleStm cmd) <++> parseExpr omap
        Nothing -> return Nothing

type VarDec = [(PosStr, Expr)]
parseVarDecs:: OpeMap -> Parser (Maybe VarDec)
parseVarDecs omap = fmap (Just . conv) parse
    where
    parse:: Parser [VarDecSet]
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: [VarDecSet] -> VarDec
    conv = concatMap (uncurry zip) . (map toTuple)
    toTuple (VarDecSet ns t) = (ns, repeat t)
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose

-- declaration parsers
data Decla = Axiom VarDec Expr | Theorem VarDec Expr Statement
    | Define PosStr VarDec Expr Expr | Predicate PosStr PosStr Expr VarDec Expr
    | DataType PosStr Expr | Undef PosStr Expr
    | InfixDecla Bool Int Int PosStr deriving (Show)

parseDeclaBody:: OpeMap -> String -> Parser (Maybe Decla)
parseDeclaBody omap "axiom" = return (Just Axiom)
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "theorem" = return (Just Theorem)
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" 
    <++> parseExpr omap
    <::> parseToken (Ident "proof") <::> parseSymbol ":" <++> parseMultiLineStm omap
    <::> parseSymbol "}"
parseDeclaBody omap "define" = return (Just Define)
    <++> parseIdent
    <++> parseParenVarDecs omap
    <::> parseSymbol ":" <++> parseExpr omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "predicate" = return (Just Predicate)
    <++> parseIdent
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap<::> parseSymbol "]"
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "data" = return (Just DataType)
    <++> parseIdent <::> parseOperator "=" <++> parseExpr omap
parseDeclaBody omap "undef" = return (Just Undef)
    <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap
parseDeclaBody omap "infixl" = return (Just (InfixDecla True 2))
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "infixr" = return (Just (InfixDecla False 2))
    <++> parseNumber <++> parseAnyOperator 
parseDeclaBody omap "unaryl" = return (Just (InfixDecla True 1))
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "unaryr" = return (Just (InfixDecla False 1))
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody _ _ = return Nothing

parseDecla:: OpeMap -> Parser (Maybe Decla)
parseDecla omap = parseIdent >>= \case
    Just (_, x)-> parseDeclaBody omap x
    Nothing -> return Nothing

-- main parser
parseProgram:: Parser ([Decla], OpeMap)
parseProgram = parseProgram' buildInOpe where
    buildInOpe = M.fromList [(">>=", (2, 0, True)), ("->", (2, 1, True)), ("|", (2, 2, True))]
    parseRest:: Decla -> OpeMap -> Parser ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> Parser ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just x@(InfixDecla leftAssoc narg pre (_, s)) -> parseRest x $ M.insert s (narg, pre, leftAssoc) omap
        Just x -> parseRest x omap
        Nothing -> return ([], omap)