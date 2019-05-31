module Parser(tokenize, parseProgram, parseExprs) where
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
import Data

popToken:: Lexer (Maybe PosToken)
popToken = Lexer $ \(pos, all) -> case all of 
    [] -> ([], pos, [], Just $ PosToken pos EndToken)
    (x:xs)
        | isDigit x -> procAll (NumberToken . read) isDigit
        | isIdentHead x -> procAll IdentToken isIdentBody
        | isOperator x -> procAll OperatorToken isOperator
        | isSymbol x -> ([], nextChar pos, xs, Just $ PosToken pos $ toSymbol [x])
        | x == '"' -> procQuote StringToken ('"' /=)
        | x == '\'' -> procQuote StringToken ('\'' /=)
        | x == '#' -> let (t, rest) = span ('\n' /=) xs in ([], stepChar pos $ length t, rest, Nothing) 
        | x == '\n' -> ([], nextLine pos, xs, Nothing)
        | isSpace x -> ([], nextChar pos, xs, Nothing)
        | otherwise -> ([Message (Ident pos [x]) "wrong"], nextChar pos, xs, Nothing)
        where
        procAll:: (String -> Token) -> (Char -> Bool) -> ([Message], Position, String, Maybe PosToken)
        procAll cstr cond = ([], newPos, rest, Just $ PosToken pos $ cstr (x:chars)) where
            newPos = stepChar pos $ length chars
            (chars, rest) = span cond xs
        procQuote:: (String -> Token) -> (Char -> Bool) -> ([Message], Position, String, Maybe PosToken)
        procQuote cstr cond = case span cond xs of
            (chars, _:rest) -> ([], stepChar pos $ length chars, rest, Just $ PosToken pos $ cstr chars)
            (chars, _) -> ([Message (Ident pos []) "not"], pos, [], Just $ PosToken pos $ cstr chars)
    where
    -- Char -> Bool
    [isIdentSymbol, isOperator, isSymbol] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$~`.&%", "(){}[],:"]
    [isIdentHead, isIdentBody] = map any [[isLetter, ('_' ==)], [isLetter, isDigit, isIdentSymbol]]
        where any = F.foldr ((<*>) . (<$>) (||)) $ const False
    -- String -> Token
    toSymbol all = case all of "(" -> ParenOpen; ")" -> ParenClose; "," -> Comma; _ -> SymbolToken all

-- string to tokens
tokenize:: Lexer [PosToken]
tokenize = do
    mtoken <- popToken
    case mtoken of
        Just token@(PosToken _ EndToken) -> return []
        Just token -> do
            rest <- tokenize
            return $ token:rest
        Nothing -> tokenize

toEmbString:: String -> EmbString
toEmbString ['$'] = [EmbVar 1]
toEmbString ('$':(x:xs)) = if isNumber x then EmbVar (read [x]):toEmbString xs else EmbVar 1:toEmbString (x:xs)
toEmbString (x:xs) = case toEmbString xs of
    (EmbStr str:ys) -> EmbStr (x:str):ys
    ys -> EmbStr [x]:ys
toEmbString x = [EmbStr x]

parseEmbString:: Parser (Maybe EmbString)
parseEmbString = do
    str <- parseStringToken
    return $ toEmbString <$> str 

-- parse expression by shunting yard algorithm
parseExpr:: OpeMap -> Parser (Maybe Expr)
parseExpr omap = Parser $ \ts-> parseExpr ts [] [] where
    -- (input tokens, operation stack, expression queue) -> (expression, rest token)
    parseExpr:: [PosToken] -> [(PosToken, Int)] -> [Expr] -> ([Message], [PosToken], Maybe Expr)
    parseExpr [] s q = ([], [], Just $ head $ makeExpr s q)
    parseExpr all@(px@(PosToken pos x):xs) s q = case x of
        NumberToken n   -> maybeEnd $ parseExpr xs s (NumExpr (IdentInt pos n):q)
        IdentToken id   -> maybeEnd $ case xs of
            (po@(PosToken _ ParenOpen):xs')-> parseExpr xs' ((po, 2):(px, 1):s) q
            _-> parseExpr xs s (IdentExpr (Ident pos id):q)
        ParenOpen       -> maybeEnd $ parseExpr xs ((px, 2):(tuple, 1):s) q -- 2 args for end condition
        ParenClose      -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            (opes, _:rest) = span ((not <$> isParenOpen) . fst) s
        Comma           -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            isIdent = \case PosToken _ (IdentToken _) -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((not <$> isParenOpen) . fst) s
        OperatorToken ope -> parseExpr xs ((px, narg):rest) $ makeExpr opes q where
            (msg, (narg, preceed, lassoc)) = getOpe $ Ident pos ope
            (opes, rest) = span (precederEq (preceed, lassoc) . fst) s
        SymbolToken{}   -> result
        where
            isParenOpen = \case PosToken _ ParenOpen -> True; _ -> False
            result = ([], all, Just $ head $ makeExpr s q)
            maybeEnd a = if sum (map ((-1+) . snd) s) + 1 == length q then result else a
    tuple = PosToken NonePosition (IdentToken "tuple")
    -- ((operator or function token, argument number), input) -> output
    makeExpr:: [(PosToken, Int)] -> [Expr] -> [Expr]
    makeExpr [] q = q
    makeExpr ((PosToken _ (IdentToken "tuple"), 1):os) q = makeExpr os q
    makeExpr ((PosToken pos t, n):os) q = makeExpr os $ FunExpr (Ident pos $ showToken t) args:rest
        where (args, rest) = (reverse $ take n q, drop n q)
    -- apply 'f' to a element that satisfy 'cond' for the first time
    apply cond f all = case b of [] -> all; (x:xs) -> a ++ f x:xs
        where (a, b) = span (not <$> cond) all
    -- String -> (preceed, left associative)
    defaultOpe = (-1, 2, True)
    getOpe:: Ident -> ([Message], (Int, Int, Bool))
    getOpe x@(Ident pos id) = maybe ([Message x "Not defined infix"], defaultOpe) ([], ) (M.lookup id omap)
    precederEq:: (Int, Bool) -> PosToken -> Bool
    precederEq _ (PosToken _ ParenOpen) = False
    precederEq _ (PosToken _ (IdentToken _)) = True
    precederEq (apre, aleft) (PosToken _ (OperatorToken t)) = aleft && ((bleft && apre <= bpre) || apre < bpre)
        where (_, bpre, bleft) = fromMaybe defaultOpe $ M.lookup t omap

-- atom parsers
parseToken:: Token -> Parser (Maybe Token)
parseToken x = Parser $ \case
    [] -> ([], [], Nothing)
    all@((PosToken _ t):ts) -> if t == x then ([], ts, Just x) else ([], all, Nothing)
parseSymbol x = parseToken (SymbolToken x)
parseOperator x = parseToken (OperatorToken x)

parseAnyOperator:: Parser (Maybe Ident)
parseAnyOperator = Parser $ \case
    [] -> ([], [], Nothing)
    (PosToken pos (OperatorToken str):ts) -> ([], ts, Just $ Ident pos str)
    all -> ([], all, Nothing)

parseNumber:: Parser (Maybe Int)
parseNumber = Parser $ \case
    [] -> ([], [], Nothing)
    all@(PosToken _ t:ts) -> case t of NumberToken n-> ([], ts, Just n); _-> ([], all, Nothing)

parseStringToken:: Parser (Maybe String)
parseStringToken = Parser $ \case
    [] -> ([], [], Nothing)
    all@(PosToken _ t:ts) -> case t of StringToken n-> ([], ts, Just n); _-> ([], all, Nothing)

parseIdent:: Parser (Maybe Ident)
parseIdent = Parser $ \case
    [] -> ([], [], Nothing)
    (PosToken _ (IdentToken "operator"):PosToken pos (OperatorToken str):ts) -> ([], ts, Just $ Ident pos str)
    (PosToken pos (IdentToken str):ts) -> ([], ts, Just $ Ident pos str)
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
    Just f -> Just . f <$> latter
    Nothing -> return Nothing

infixl 1 <::>
(<::>):: Parser (Maybe a) -> Parser (Maybe b) -> Parser (Maybe a)
former <::> latter = former >>= \case
    Just f -> latter >>= \case
            Just x -> return $ Just f
            Nothing -> return Nothing
    Nothing -> return Nothing

infixl 1 <!!>
(<!!>):: Parser (Maybe (Maybe a -> b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <!!> latter = former >>= \case
    Just f -> latter >>= \case
            Just x -> return $ Just (f $ Just x)
            Nothing -> return $ Just (f Nothing)
    Nothing -> return Nothing

parseSequence:: Parser (Maybe a) -> Parser [a]
parseSequence p = p >>= \case
    Just x' -> (x':) <$> parseSequence p
    Nothing -> return []

parseCommaSeparated:: Parser (Maybe a) -> Parser [a]
parseCommaSeparated = parseSeparated $ parseToken Comma

parseVarDecSet:: OpeMap -> Parser (Maybe VarDecSet)
parseVarDecSet omap = return (Just VarDecSet) <&&> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr omap

parseMultiLineStm:: OpeMap -> Parser (Maybe [IdentStm])
parseMultiLineStm omap = Just <$> parseSequence (parseStatement omap)

parseStatement:: OpeMap -> Parser (Maybe IdentStm)
parseStatement omap = parseCmd >>= \case
    Just idCmd@(IdentCmd id _) -> parseIdent >>= ((fmap $ IdentStm id) <$> ) . \case
        Just (Ident _ "assume") -> return (Just $ AssumeStm idCmd)
            <++> parseExpr omap <::> parseSymbol "{"
            <++> parseBlock <::> parseSymbol "}"
        _ -> return (Just $ CmdStm idCmd) <++> parseExpr omap
    Nothing -> return Nothing
    where
    parseCmd:: Parser (Maybe IdentCmd)
    parseCmd = parseIdent >>= \case
        Just id@(Ident _ "step") -> return $ Just $ IdentCmd id StepCmd
        Just id@(Ident _ "impl") -> return $ Just $ IdentCmd id ImplCmd
        Just id@(Ident _ "begin") -> return $ Just $ IdentCmd id BeginCmd
        Just id@(Ident _ "target") -> return $ Just $ IdentCmd id TargetCmd
        Just id@Ident{} -> return $ Just $ IdentCmd id WrongCmd
        Nothing -> return Nothing
    parseBlock:: Parser (Maybe [IdentStm])
    parseBlock = return (Just id) <::> parseSymbol "{" <&&> parseSequence (parseStatement omap) <::> parseSymbol "}"

parseVarDecs:: OpeMap -> Parser (Maybe VarDec)
parseVarDecs omap = fmap (Just . conv) parse
    where
    parse:: Parser [VarDecSet]
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: [VarDecSet] -> VarDec
    conv = concatMap (uncurry zip) . (map toTuple)
    toTuple (VarDecSet ns t) = (ns, repeat t)
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose
parseParenVarDecsSet omap = fmap Just $ parseSequence $ parseParenVarDecs omap

parseLatex:: Parser (Maybe EmbString)
parseLatex = return (Just id) <::> parseToken (IdentToken "latex") <++> parseEmbString

parseDeclaBody:: OpeMap -> String -> Parser (Maybe Decla)
parseDeclaBody omap "axiom" = return (Just Axiom)
    <++> parseParenVarDecsSet omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "theorem" = return (Just Theorem)
    <++> parseParenVarDecsSet omap
    <::> parseSymbol "{" 
    <++> parseExpr omap
    <::> parseToken (IdentToken "proof") <::> parseSymbol ":" <++> parseMultiLineStm omap
    <::> parseSymbol "}"
parseDeclaBody omap "define" = return (Just Define)
    <++> parseIdent
    <++> parseParenVarDecsSet omap
    <::> parseSymbol ":" <++> parseExpr omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "predicate" = return (Just Predicate)
    <++> parseIdent
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap<::> parseSymbol "]"
    <++> parseParenVarDecsSet omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "data" = return (Just DataType)
    <++> parseIdent <::> parseOperator "=" <++> parseExpr omap
parseDeclaBody omap "undef" = return (Just Undef)
    <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap <!!> parseLatex
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
    Just (Ident _ x)-> parseDeclaBody omap x
    Nothing -> return Nothing

parseProgramNoLex:: Parser ([Decla], OpeMap)
parseProgramNoLex = parseProgram' buildInOpe where
    buildInOpe = M.fromList [(">>=", (2, 0, True)), ("->", (2, 1, True)), ("|", (2, 2, True)), (".", (2, 100, True))]
    parseRest:: Decla -> OpeMap -> Parser ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> Parser ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just x@(InfixDecla leftAssoc narg pre (Ident _ s)) -> parseRest x $ M.insert s (narg, pre, leftAssoc) omap
        Just x -> parseRest x omap
        Nothing -> return ([], omap)

parseProgram:: String -> ([Message], [Decla], OpeMap)
parseProgram prg = (msg ++ msg', declas, omap) where
    (msg, pos, rest, tokens) = runLexer tokenize (initialPosition, prg)
    (msg', rest', (declas, omap)) = runParser parseProgramNoLex tokens

lexer str = (\(_, _, _, x)-> x) $ runLexer tokenize (initialPosition, str)
parser p t = (\(_, _, x)-> x) $ runParser p t

tokenizeTest line = intercalate "," $ map show $ lexer line
parserTest x = show . parser x . lexer

parseExprs:: OpeMap -> String -> [Expr]
parseExprs omap str = (\(_, _, x)-> x) (runParser (parseCommaSeparated $ parseExpr omap) $ lexer str)