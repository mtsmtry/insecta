module Parser.Combinater where
import Parser.Data

-- Monad
newtype Parser a = Parser { runParser::[PosToken] -> ([Message], [PosToken], a) }

instance Functor Parser where
    fmap f (Parser g) = Parser $ \inTok -> let (msg, tok, x) = g inTok in (msg, tok, f x)

instance Applicative Parser where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad Parser where
    return x = Parser ([], , x)
    (Parser h) >>= f = Parser $ \inTok ->
        let (msg, tok, x) = h inTok
            (Parser g) = f x
            (msg', tok', x') = g tok
        in  (msg ++ msg', tok', x')
        
-- Atoms
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

-- Combinaters
infixl 1 >>=>
(>>=>):: Monad m => m (Maybe a) -> (a -> m (Maybe b)) -> m (Maybe b)
a >>=> b = a >>= maybe (return Nothing) b

infixl 1 <++>
(<++>):: Parser (Maybe (a->b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <++> latter = former >>=> \f -> latter >>=> \x -> return $ Just (f x)

infixl 1 <&&>
(<&&>):: Parser (Maybe (a->b)) -> Parser a -> Parser (Maybe b)
former <&&> latter = former >>=> \f -> Just . f <$> latter

infixl 1 <::>
(<::>):: Parser (Maybe a) -> Parser (Maybe b) -> Parser (Maybe a)
former <::> latter = former >>=> \f -> latter >>=> const (return $ Just f)

infixl 1 <!!>
(<!!>):: Parser (Maybe (Maybe a -> b)) -> Parser (Maybe a) -> Parser (Maybe b)
former <!!> latter = former >>=> \f -> latter >>= \case
    Just x -> return $ Just (f $ Just x)
    Nothing -> return $ Just (f Nothing)

-- Parsers
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

rollback:: Parser (Maybe a) -> (a -> Parser (Maybe b)) -> Parser (Maybe b)
rollback (Parser first) second = Parser $ \ts -> case first ts of
    (msg1, ts1, Just res1) -> let (Parser g) = second res1 in case g ts1 of
        all@(msg2, ts2, Just res2) -> (msg1 ++ msg2, ts2, Just res2)
        _ -> ([], ts, Nothing)
    _ -> ([], ts, Nothing)