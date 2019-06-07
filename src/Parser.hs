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
        | isDigit x     -> procAll (NumberToken . read) isDigit
        | isIdentHead x -> procAll IdentToken isIdentBody
        | isOperator x  -> procAll OperatorToken isOperator
        | isSymbol x    -> ([], nextChar pos, xs, Just $ PosToken pos $ toSymbol [x])
        | x == '"'  -> procQuote StringToken ('"' /=)
        | x == '\'' -> procQuote StringToken ('\'' /=)
        | x == '#'  -> let (t, rest) = span ('\n' /=) xs in ([], stepChar pos $ length t, rest, Nothing) 
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

tokenize:: Lexer [PosToken]
tokenize = popToken >>= \case
    Just token@(PosToken _ EndToken) -> return []
    Just token -> (token:) <$> tokenize
    Nothing -> tokenize

toEmbString:: String -> EmbString
toEmbString ['$'] = [EmbVar 1]
toEmbString ('$':(x:xs)) = if isNumber x then EmbVar (read [x]):toEmbString xs else EmbVar 1:toEmbString (x:xs)
toEmbString (x:xs) = case toEmbString xs of
    (EmbStr str:ys) -> EmbStr (x:str):ys
    ys -> EmbStr [x]:ys
toEmbString x = [EmbStr x]

parseEmbString:: Parser (Maybe EmbString)
parseEmbString = (toEmbString <$>) <$> parseStringToken

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
        ParenClose      -> maybeEnd $ case span ((not <$> isParenOpen) . fst) s of
            (opes, _:rest) -> parseExpr xs rest $ makeExpr opes q
            (_, []) -> ([Message (Ident pos $ showToken x) "括弧が揃っていません"], all, Nothing)
        Comma           -> maybeEnd $ parseExpr xs rest $ makeExpr opes q where
            isIdent      = \case PosToken _ (IdentToken _) -> True; _ -> False
            incrementArg = apply (isIdent . fst) (fmap (1+))
            (opes, rest) = incrementArg <$> span ((not <$> isParenOpen) . fst) s
        OperatorToken ope -> parseExpr xs ((px, narg):rest) $ makeExpr opes q where
            (msg, Operator narg preceed lassoc) = getOpe $ Ident pos ope
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
    getOpe:: Ident -> ([Message], Operator)
    getOpe x@(Ident pos id) = maybe ([Message x "Not defined infix"], defaultOpe) ([], ) (M.lookup id omap)
    precederEq:: (Int, Bool) -> PosToken -> Bool
    precederEq _ (PosToken _ ParenOpen) = False
    precederEq _ (PosToken _ (IdentToken _)) = True
    precederEq (apre, aleft) (PosToken _ (OperatorToken t)) = aleft && ((bleft && apre <= bpre) || apre < bpre)
        where Operator _ bpre bleft = fromMaybe defaultOpe $ M.lookup t omap

-- atom parsers
parseOne:: ((Position, Token) -> Maybe a) -> Parser (Maybe a)
parseOne f = Parser $ \case
    [] -> ([], [], Nothing)
    all@(PosToken pos t:ts) -> maybe ([], all, Nothing) (([], ts, ) . Just) $ f (pos, t)

parseToken:: Token -> Parser (Maybe Token)
parseToken x = parseOne $ \(pos, tok)-> if tok == x then Just x else Nothing
parseSymbol:: String -> Parser (Maybe Token)
parseSymbol x = parseToken (SymbolToken x)
parseOperator:: String -> Parser (Maybe Token)
parseOperator x = parseToken (OperatorToken x)
parseAnyOperator:: Parser (Maybe Ident)
parseAnyOperator = parseOne $ \case (pos, OperatorToken str)-> Just $ Ident pos str; _ -> Nothing
parseNumber:: Parser (Maybe Int)
parseNumber = parseOne $ \case (_, NumberToken num)-> Just num; _ -> Nothing
parseStringToken:: Parser (Maybe String)
parseStringToken = parseOne $ \case (_, StringToken str)-> Just str; _ -> Nothing
parseIdent:: Parser (Maybe Ident)
parseIdent = parseOne (\case (pos, IdentToken str)-> Just $ Ident pos str; _ -> Nothing)
    >>=> \id-> if idStr id == "operator" then parseAnyOperator else return $ Just id
parseSeparated:: Parser (Maybe s) -> Parser (Maybe a) -> Parser [a]
parseSeparated s p = p >>= maybe (return []) (\item -> s >>= maybe (return [item]) 
    (const $ parseSeparated s p >>= \rest -> return (item:rest)))

-- parser connecters
infixl 1 >>=>; infixl 1 <++>; infixl 1 <&&>; infixl 1 <::>; infixl 1 <!!>
(>>=>):: Monad m => m (Maybe a) -> (a -> m (Maybe b)) -> m (Maybe b)
a >>=> b = a >>= maybe (return Nothing) b
(<++>):: Parser (Maybe (a->b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <++> latter = former >>=> \f -> latter >>=> \x -> return $ Just (f x)
(<&&>):: Parser (Maybe (a->b)) -> Parser a -> Parser (Maybe b)
former <&&> latter = former >>=> \f -> Just . f <$> latter
(<::>):: Parser (Maybe a) -> Parser (Maybe b) -> Parser (Maybe a)
former <::> latter = former >>=> \f -> latter >>=> const (return $ Just f)
(<!!>):: Parser (Maybe (Maybe a -> b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <!!> latter = former >>=> \f -> latter >>= \case
    Just x -> return $ Just (f $ Just x)
    Nothing -> return $ Just (f Nothing)

-- parsers
parseSwitch:: (String -> Maybe (Parser (Maybe a))) -> Parser (Maybe a) -> Parser (Maybe a)
parseSwitch switch other = Parser $ \case
    [] -> ([], [], Nothing)
    all@(PosToken _ (IdentToken str):ts) -> case switch str of
        Just parser -> runParser parser ts
        Nothing -> runParser other all
    all -> runParser other all

parseSequence:: Parser (Maybe a) -> Parser [a]
parseSequence p = p >>= \case
    Just x' -> (x':) <$> parseSequence p
    Nothing -> return []

parseCommaSeparated:: Parser (Maybe a) -> Parser [a]
parseCommaSeparated = parseSeparated $ parseToken Comma

parseTypingKind:: Parser (Maybe TypingKind)
parseTypingKind = do
    sem <- parseSymbol ":"
    if isNothing sem then return Nothing else do
        ope <- parseToken (OperatorToken ">")
        return $ Just $ if isNothing ope then NormalTyping else ExtendTyping

parseVarDecSet:: OpeMap -> Parser (Maybe VarDecSet)
parseVarDecSet omap = return (Just VarDecSet) <&&> parseCommaSeparated parseIdent <++> parseTypingKind <++> parseExpr omap

parseMultiLineStm:: OpeMap -> Parser (Maybe [IdentWith Statement])
parseMultiLineStm omap = Just <$> parseSequence (parseStatement omap)

parseDefineBody:: OpeMap -> Parser (Maybe DefineBody)
parseDefineBody omap = return (Just DefineBody) <&&> parseSequence (parseStatement omap) <++> parseExpr omap

parseStatement:: OpeMap -> Parser (Maybe (IdentWith Statement))
parseStatement omap = parseCmd >>= \case
        Nothing -> parseIdent `rollback` \id-> withIdent id $ case idStr id of
            "forall" -> return (Just ForAllStm) <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap
            "exists" -> return (Just ExistsStm) <++> parseIdent
                        <::> parseSymbol "[" <&&> parseCommaSeparated parseIdent <::> parseSymbol "]"
                        <::> parseSymbol ":" <++> parseExpr omap    
            _ -> return Nothing
        Just idCmd -> withIdent (fst idCmd) $ parseSwitch (switch idCmd) (other idCmd)
    where
    switch idCmd = \case
        "assume" -> Just $ return (Just $ AssumeStm idCmd) <++> parseExpr omap <++> parseBlock
        _ -> Nothing
    other idCmd = return (Just $ CmdStm idCmd) <++> parseExpr omap
    parseCmd:: Parser (Maybe (IdentWith Command))
    parseCmd = parseIdent `rollback` (\id@(Ident _ str)-> (return . (\case WrongCmd->Nothing; cmd-> Just (id, cmd)) . cmdCase) str)
        where cmdCase = \case "step" -> StepCmd; "impl"  -> ImplCmd;  "unfold" -> UnfoldCmd; 
                              "fold" -> FoldCmd; "begin" -> BeginCmd; "target" -> TargetCmd; _-> WrongCmd
    parseBlock:: Parser (Maybe [IdentWith Statement])
    parseBlock = return (Just id) <::> parseSymbol "{" <&&> parseSequence (parseStatement omap) <::> parseSymbol "}"
    withIdent:: Ident -> Parser (Maybe a) -> Parser (Maybe (IdentWith a))
    withIdent id parse = parse >>= \case
        Just item -> return $ Just (id, item)
        Nothing -> return Nothing

parseVarDecs:: OpeMap -> Parser (Maybe [VarDec])
parseVarDecs omap = fmap (Just . conv) parse
    where
    parse:: Parser [VarDecSet]
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: [VarDecSet] -> [VarDec]
    conv = (map make) . concatMap (uncurry zip) . (map toTuple)
    make (name, (kind, ty)) = VarDec kind name ty
    toTuple (VarDecSet names kind ty) = (names, repeat (kind, ty))
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose
parseParenVarDecsSet omap = fmap Just $ parseSequence $ parseParenVarDecs omap

parseLatex:: Parser (Maybe EmbString)
parseLatex = return (Just id) <::> parseToken (IdentToken "latex") <++> parseEmbString

parseDeclaBody:: OpeMap -> String -> Parser (Maybe Decla)
parseDeclaBody omap "axiom" = return (Just AxiomDecla) <++> parseParenVarDecsSet omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "theorem" = return (Just TheoremDecla) <++> parseParenVarDecsSet omap
    <::> parseSymbol "{" <++> parseExpr omap
    <::> parseToken (IdentToken "proof") <::> parseSymbol ":" <++> parseMultiLineStm omap <::> parseSymbol "}"
parseDeclaBody omap "fun" = return (Just DefineDecla) <++> parseIdent <++> parseParenVarDecsSet omap
    <::> parseSymbol ":" <++> parseExpr omap
    <::> parseSymbol "{" <++> parseDefineBody omap <::> parseSymbol "}"
parseDeclaBody omap "pred" = return (Just PredicateDecla) <++> parseIdent <++> parseParenVarDecsSet omap
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap <::> parseSymbol "]"
    <::> parseSymbol "{" <++> parseDefineBody omap <::> parseSymbol "}"
parseDeclaBody omap "data" = return (Just DataTypeDecla)
    <++> parseIdent <::> parseOperator "=" <++> parseExpr omap
parseDeclaBody omap "undef" = return (Just UndefDecla) <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap <!!> parseLatex
parseDeclaBody omap "infixl" = return (Just (InfixDecla True 2))  <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "infixr" = return (Just (InfixDecla False 2)) <++> parseNumber <++> parseAnyOperator 
parseDeclaBody omap "unaryl" = return (Just (InfixDecla True 1))  <++> parseNumber <++> parseAnyOperator
parseDeclaBody omap "unaryr" = return (Just (InfixDecla False 1)) <++> parseNumber <++> parseAnyOperator
parseDeclaBody _ _ = return Nothing

parseDecla:: OpeMap -> Parser (Maybe Decla)
parseDecla omap = parseIdent >>= \case
    Just (Ident _ x)-> parseDeclaBody omap x
    Nothing -> return Nothing

parseProgramNoLex:: Parser ([Decla], OpeMap)
parseProgramNoLex = parseProgram' buildInOpe where
    parseRest:: Decla -> OpeMap -> Parser ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> Parser ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just x@(InfixDecla leftAssoc narg pre (Ident _ s)) -> parseRest x $ M.insert s (Operator narg pre leftAssoc) omap
        Just x -> parseRest x omap
        Nothing -> return ([], omap)

parseProgram:: String -> ([Message], [Decla], OpeMap)
parseProgram prg = (msg ++ msg', declas, omap) where
    (msg, pos, rest, tokens) = runLexer tokenize (initialPosition, prg)
    (msg', rest', (declas, omap)) = runParser parseProgramNoLex tokens

parseExprs:: OpeMap -> String -> [Expr]
parseExprs omap str = (\(_, _, x)-> x) (runParser (parseCommaSeparated $ parseExpr omap) $ lexer str) where
    lexer str = (\(_, _, _, x)-> x) $ runLexer tokenize (initialPosition, str)