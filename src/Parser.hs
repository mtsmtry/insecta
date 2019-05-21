module Parser where
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
    [isIdentSymbol, isOperator, isSymbol] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$~`.&", "(){}[],:"]
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
type OpeMap = M.Map String (Int, Bool)
data ExprHead = ExprHead PosStr Int | PureExprHead PosStr deriving (Show)

showHead:: ExprHead -> String
showHead (ExprHead (_, t) _) = t
showHead (PureExprHead (_, t)) = t

-- Expression
-- has position on code
data Expr = IdentExpr PosStr | FuncExpr ExprHead [Expr] 
        | StringExpr PosStr | NumberExpr Position Int | Rewrite Rule Expr Expr deriving (Show)

makeExprHead:: String -> ExprHead
makeExprHead = PureExprHead . makePosStr

makeIdentExpr:: String -> Expr
makeIdentExpr = IdentExpr . makePosStr

getPosAndStr:: Expr -> PosStr
getPosAndStr (IdentExpr ps) = ps
getPosAndStr (StringExpr ps) = ps
getPosAndStr (NumberExpr p n) = (p, show n)
getPosAndStr (Rewrite _ a _) = getPosAndStr a
getPosAndStr (FuncExpr (ExprHead ps _) _) = ps
getPosAndStr (FuncExpr (PureExprHead ps) _) = ps

-- parse expression by shunting yard algorithm        
parseExpr:: OpeMap -> State [PosToken] (Maybe Expr)
parseExpr omap = state $ \ts-> parseExpr ts [] [] where
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [PosToken] -> [(PosToken, Int)] -> [Expr] -> (Maybe Expr, [PosToken])
    parseExpr [] s q = (Just $ head $ makeExpr s q, [])
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
        Operator ope  -> parseExpr xs ((px, 2):rest) $ makeExpr opes q where
                (opes, rest) = span (precederEq ope . fst) s
        Symbol{}  -> result
        where
            isParenOpen = \case PosToken _ ParenOpen -> True; _ -> False
            result = (Just $ head $ makeExpr s q, all)
            maybeEnd a = if sum (map ((-1+) . snd) s) + 1 == length q then result else a
    tuple = PosToken NonePosition (Ident "tuple")
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(PosToken, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((PosToken _ (Ident "tuple"), 1):os) q = makeExpr os q
    makeExpr ((PosToken p t, n):os) q = makeExpr os $ FuncExpr (PureExprHead (p, showToken t)) args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all
    -- String -> (preceed, left associative)
    getOpe x = fromMaybe (0, True) $ M.lookup x $ M.union buildInOpe omap -- todo output message
    buildInOpe = M.fromList [(">>=", (0, True)), ("->", (1, True)), ("|", (2, True))]
    precederEq:: String -> PosToken -> Bool
    precederEq s (PosToken _ ParenOpen) = False
    precederEq s (PosToken _ (Ident _)) = True
    precederEq s (PosToken _ (Operator t)) = precederEq' $ map getOpe [s, t] where
        precederEq' [(aPre, aLeft), (bPre, bLeft)] = bLeft && ((aLeft && aPre <= bPre) || aPre < bPre)

-- atom parsers
parseToken:: Token -> State [PosToken] (Maybe Token)
parseToken x = state $ \case
    [] -> (Nothing, [])
    all@((PosToken _ t):ts) -> if t == x then (Just x, ts) else (Nothing, all)
parseSymbol x = parseToken (Symbol x)
parseOperator x = parseToken (Operator x)

parseAnyOperator:: State [PosToken] (Maybe PosStr)
parseAnyOperator = state $ \case
    [] -> (Nothing, [])
    (PosToken p (Operator s):ts) -> (Just (p, s), ts)
    all -> (Nothing, all)

parseNumber:: State [PosToken] (Maybe Int)
parseNumber = state $ \case
    [] -> (Nothing, [])
    all@((PosToken _ t):ts) -> case t of Number n-> (Just n, ts); _-> (Nothing, all)

parseIdent:: State [PosToken] (Maybe PosStr)
parseIdent = state $ \case
    [] -> (Nothing, [])
    (PosToken _ (Ident "operator"):PosToken p (Operator s):ts) -> (Just (p, s), ts)
    (PosToken p (Ident s):ts) -> (Just (p, s), ts)
    all -> (Nothing, all)

parseSeparated:: State [PosToken] (Maybe s) -> State [PosToken] (Maybe a) -> State [PosToken] (Maybe [a]) 
parseSeparated s p = p >>= \case
    Just x' -> s >>= \case
        Just _ -> parseSeparated s p >>= \case
            Just r' -> return $ Just (x':r')
            Nothing -> return Nothing
        Nothing -> return $ Just [x']
    Nothing -> return $ Just []

-- parser connecters
infixl 1 <++>
(<++>):: State [PosToken] (Maybe (a->b)) -> State [PosToken] (Maybe a) -> State [PosToken] (Maybe b)
f <++> a = f >>= maybe (return Nothing) (\f'-> fmap f' <$> a)

infixl 1 <::>
(<::>):: State [PosToken] (Maybe a) -> State [PosToken] (Maybe b) -> State [PosToken] (Maybe a)
f <::> a = f >>= maybe (return Nothing) (\f'-> maybe Nothing (const $ Just f') <$> a)

parseSequence:: State [PosToken] (Maybe a)-> State [PosToken] (Maybe [a])
parseSequence p = p >>= \case
    Just x' -> parseSequence p >>= \case
        Just s' -> return $ Just (x':s')
        Nothing -> return Nothing
    Nothing -> return $ Just []

parseCommaSeparated:: State [PosToken] (Maybe a) -> State [PosToken] (Maybe [a]) 
parseCommaSeparated = parseSeparated $ parseToken Comma

-- parser parts
data VarDecSet = VarDecSet [PosStr] Expr deriving (Show)
parseVarDecSet:: OpeMap -> State [PosToken] (Maybe VarDecSet)
parseVarDecSet omap = return (Just VarDecSet) <++> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr omap

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

parseMultiLineStm:: OpeMap -> State [PosToken] (Maybe Statement)
parseMultiLineStm omap = return (Just BlockStm) <++> parseSequence (parseStatement omap)

parseStatement:: OpeMap -> State [PosToken] (Maybe Statement)
parseStatement omap = parseSymbol "{" >>= \case 
    Just{} -> parseBlock
    Nothing -> parseSingleStm
    where
    parseCmd = parseIdent >>= \case
        Just (_, "step") -> return $ Just StepCmd
        Just (_, "impl") -> return $ Just ImplCmd
        Just (_, s) -> return $ Just $ WrongCmd s
    parseBlock = return (Just BlockStm) <++> parseSequence (parseStatement omap) <::> parseSymbol "}"
    parseSingleStm = parseCmd >>= \case
        Just cmd -> parseIdent >>= \case
            Just (_, "assume") -> return (Just $ AssumeStm cmd) 
                <++> parseExpr omap <::> parseSymbol "{"
                <::> parseToken (Ident "begin") <++> parseExpr omap 
                <++> parseMultiLineStm omap <::> parseSymbol "}"
            _ -> return (Just $ SingleStm cmd) <++> parseExpr omap
        Nothing -> return Nothing

type VarDec = [(PosStr, Expr)]
parseVarDecs:: OpeMap -> State [PosToken] (Maybe VarDec)
parseVarDecs omap = fmap conv parse where
    parse:: State [PosToken] (Maybe [VarDecSet])
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: Maybe [VarDecSet] -> Maybe VarDec
    conv = Just . concatMap (uncurry zip) . maybe [] (map toTuple)
    toTuple (VarDecSet ns t) = (ns, repeat t)
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose

-- declaration parsers
data Decla = Axiom VarDec Expr | Theorem VarDec Expr Statement
    | Define PosStr VarDec Expr Expr | Predicate PosStr PosStr Expr VarDec Expr
    | DataType PosStr Expr | Undef PosStr Expr
    | InfixDecla Bool PosStr Int PosStr deriving (Show)

parseDeclaBody:: OpeMap -> String -> State [PosToken] (Maybe Decla)
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
parseDeclaBody omap "infixl" = return (Just $ InfixDecla True)
    <++> parseAnyOperator <++> parseNumber <::> parseOperator "=>" <++> parseIdent
parseDeclaBody omap "infixr" = return (Just $ InfixDecla False)
    <++> parseAnyOperator <++> parseNumber <::> parseOperator "=>" <++> parseIdent
parseDeclaBody _ _ = return Nothing

parseDecla:: OpeMap -> State [PosToken] (Maybe Decla)
parseDecla omap = parseIdent >>= \case (Just (_, x))-> parseDeclaBody omap x; _ -> return Nothing

-- main parser
parseProgram:: State [PosToken] ([Decla], OpeMap)
parseProgram = parseProgram' M.empty where
    parseRest:: Decla -> OpeMap -> State [PosToken] ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> State [PosToken] ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just x@(InfixDecla leftAssoc (_, s) pre fun) -> parseRest x $ M.insert s (pre, leftAssoc) omap
        Just x -> parseRest x omap
        Nothing -> return ([], omap)