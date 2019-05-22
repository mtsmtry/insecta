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
parseExpr:: OpeMap -> State [PosToken] (Maybe ([Message], Expr))
parseExpr omap = state $ \ts-> parseExpr ts [] [] where
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [PosToken] -> [(PosToken, Int)] -> [Expr] -> (Maybe ([Message], Expr), [PosToken])
    parseExpr [] s q = (Just ([], head $ makeExpr s q), [])
    parseExpr all@(px@(PosToken p x):xs) s q = case x of
        Error t m   -> (Nothing, all)
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
            result = (Just ([], head $ makeExpr s q), all)
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
parseToken:: Token -> State [PosToken] (Maybe ([Message], Token))
parseToken x = state $ \case
    [] -> (Nothing, [])
    all@((PosToken _ t):ts) -> if t == x then (Just ([], x), ts) else (Nothing, all)
parseSymbol x = parseToken (Symbol x)
parseOperator x = parseToken (Operator x)

parseAnyOperator:: State [PosToken] (Maybe ([Message], PosStr))
parseAnyOperator = state $ \case
    [] -> (Nothing, [])
    (PosToken p (Operator s):ts) -> (Just ([], (p, s)), ts)
    all -> (Nothing, all)

parseNumber:: State [PosToken] (Maybe ([Message], Int))
parseNumber = state $ \case
    [] -> (Nothing, [])
    all@((PosToken _ t):ts) -> case t of Number n-> (Just ([], n), ts); _-> ( Nothing, all)

parseIdent:: State [PosToken] (Maybe ([Message], PosStr))
parseIdent = state $ \case
    [] -> (Nothing, [])
    (PosToken _ (Ident "operator"):PosToken p (Operator s):ts) -> (Just ([], (p, s)), ts)
    (PosToken p (Ident s):ts) -> (Just ([], (p, s)), ts)
    all -> (Nothing, all)

parseSeparated:: State [PosToken] (Maybe ([Message], s)) -> State [PosToken] (Maybe ([Message], a)) -> State [PosToken] (Maybe ([Message], [a]))
parseSeparated s p = p >>= \case
    Just (m, x') -> s >>= \case
        Just _ -> parseSeparated s p >>= \case
            Just (m', r') -> return $ Just (m ++ m', (x':r'))
            Nothing -> return Nothing
        Nothing -> return $ Just (m, [x'])
    Nothing -> return $ Just ([], [])

-- parser connecters
infixl 1 <++>
(<++>):: State [PosToken] (Maybe ([Message], (a->b))) -> State [PosToken] (Maybe ([Message], a)) -> State [PosToken] (Maybe ([Message], b))
former <++> latter = former >>= \case
    Just (m, f) -> latter >>= \case
            Just (m', x) -> return $ Just (m ++ m', f x)
            Nothing -> return Nothing
    Nothing -> return Nothing

infixl 1 <::>
(<::>):: State [PosToken] (Maybe ([Message], a)) -> State [PosToken] (Maybe ([Message], b)) -> State [PosToken] (Maybe ([Message], a))
former <::> latter = former >>= \case
    Just (m, f) -> latter >>= \case
            Just (m', x) -> return $ Just (m ++ m', f)
            Nothing -> return Nothing
    Nothing -> return Nothing

parseSequence:: State [PosToken] (Maybe ([Message], a)) -> State [PosToken] (Maybe ([Message], [a]))
parseSequence p = p >>= \case
    Just (m, x') -> parseSequence p >>= \case
        Just (m', s') -> return $ Just (m ++ m', x':s')
        Nothing -> return Nothing
    Nothing -> return $ Just ([], [])

parseCommaSeparated:: State [PosToken] (Maybe ([Message], a)) -> State [PosToken] (Maybe ([Message], [a]))
parseCommaSeparated = parseSeparated $ parseToken Comma

-- parser parts
data VarDecSet = VarDecSet [PosStr] Expr deriving (Show)
parseVarDecSet:: OpeMap -> State [PosToken] (Maybe ([Message], VarDecSet))
parseVarDecSet omap = makeParser VarDecSet <++> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr omap

-- [proof] = [command] [expr] [command] [expr]

-- [proof]
-- [command] assume [expr] {
--     being [expr]
--     [multi-proof]
-- }

-- [proof]
-- fork [proof]
-- fork [proof]

data Command = StepCmd | ImplCmd | WrongCmd String deriving (Show)
data Statement = SingleStm Command Expr
    | BlockStm [Statement]
    | AssumeStm Command Expr Expr Statement
    | ForkStm [Statement] deriving (Show)

makeParser f = return $ Just ([], f)

parseMultiLineStm:: OpeMap -> State [PosToken] (Maybe ([Message], Statement))
parseMultiLineStm omap = makeParser BlockStm <++> parseSequence (parseStatement omap)

parseStatement:: OpeMap -> State [PosToken] (Maybe ([Message], Statement))
parseStatement omap = parseSymbol "{" >>= \case 
    Just{} -> parseBlock
    Nothing -> parseSingleStm
    where
    parseCmd = parseIdent >>= \case
        Just (_, (_, "step")) -> return $ Just StepCmd
        Just (_, (_, "impl")) -> return $ Just ImplCmd
        Just (_, (_, s)) -> return $ Just $ WrongCmd s
    parseBlock = makeParser BlockStm <++> parseSequence (parseStatement omap) <::> parseSymbol "}"
    parseSingleStm = parseCmd >>= \case
        Just cmd -> parseIdent >>= \case
            Just (_, (_, "assume")) -> makeParser (AssumeStm cmd)
                <++> parseExpr omap <::> parseSymbol "{"
                <::> parseToken (Ident "begin") <++> parseExpr omap 
                <++> parseMultiLineStm omap <::> parseSymbol "}"
            _ -> makeParser (SingleStm cmd) <++> parseExpr omap
        Nothing -> return Nothing

type VarDec = [(PosStr, Expr)]
parseVarDecs:: OpeMap -> State [PosToken] (Maybe ([Message], VarDec))
parseVarDecs omap = parse >>= \case
    Just (m, x) -> return $ Just (m, conv x)
    Nothing -> return $ Just ([], [])
    where
    parse:: State [PosToken] (Maybe ([Message], [VarDecSet]))
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: [VarDecSet] -> VarDec
    conv = concatMap (uncurry zip) . (map toTuple)
    toTuple (VarDecSet ns t) = (ns, repeat t)
parseParenVarDecs omap = makeParser id <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose

-- declaration parsers
data Decla = Axiom VarDec Expr | Theorem VarDec Expr Statement
    | Define PosStr VarDec Expr Expr | Predicate PosStr PosStr Expr VarDec Expr
    | DataType PosStr Expr | Undef PosStr Expr
    | InfixDecla Bool Int Int PosStr deriving (Show)

parseDeclaBody:: OpeMap -> String -> State [PosToken] (Maybe ([Message], Decla))
parseDeclaBody omap "axiom" = makeParser Axiom
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "theorem" = makeParser Theorem
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" 
    <++> parseExpr omap
    <::> parseToken (Ident "proof") <::> parseSymbol ":" <++> parseMultiLineStm omap
    <::> parseSymbol "}"
parseDeclaBody omap "define" = makeParser Define
    <++> parseIdent
    <++> parseParenVarDecs omap
    <::> parseSymbol ":" <++> parseExpr omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "predicate" = makeParser Predicate
    <++> parseIdent
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap<::> parseSymbol "]"
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "data" = makeParser DataType
    <++> parseIdent <::> parseOperator "=" <++> parseExpr omap
parseDeclaBody omap "undef" = makeParser Undef
    <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap
parseDeclaBody omap "infixl" = makeParser (InfixDecla True 2)
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "infixr" = makeParser (InfixDecla False 2)
    <++> parseNumber <++> parseAnyOperator 
parseDeclaBody omap "unaryl" = makeParser (InfixDecla True 1)
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "unaryr" = makeParser (InfixDecla False 1)
    <++> parseNumber <++> parseAnyOperator
parseDeclaBody _ _ = return Nothing

parseDecla:: OpeMap -> State [PosToken] (Maybe ([Message], Decla))
parseDecla omap = parseIdent >>= \case
    Just (msgs, (_, x))-> parseDeclaBody omap x
    Nothing -> return Nothing

-- main parser
parseProgram:: State [PosToken] ([Decla], OpeMap)
parseProgram = parseProgram' buildInOpe where
    buildInOpe = M.fromList [(">>=", (2, 0, True)), ("->", (2, 1, True)), ("|", (2, 2, True))]
    parseRest:: Decla -> OpeMap -> State [PosToken] ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> State [PosToken] ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just (m, x@(InfixDecla leftAssoc narg pre (_, s))) -> parseRest x $ M.insert s (narg, pre, leftAssoc) omap
        Just (m, x) -> parseRest x omap
        Nothing -> return ([], omap)