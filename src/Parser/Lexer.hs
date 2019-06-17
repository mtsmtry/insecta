module Parser.Lexer(tokenize) where
import Parser.Data
import qualified Data.Foldable as F

-- Position
initialPosition = Position 1 1
stepChar (Position l c) n = Position l (c+n)
nextChar (Position l c) = Position l (c+1)
nextLine (Position l c) = Position (l+1) 1

-- Monad
newtype Lexer a = Lexer { runLexer::(Position, String) -> ([Message], Position, String, a) }

instance Functor Lexer where
    fmap f (Lexer g) = Lexer $ \inStr -> let (msg, pos, str, x) = g inStr in (msg, pos, str, f x)

instance Applicative Lexer where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad Lexer where
    return x = Lexer $ \(pos, str) -> ([], pos, str, x)
    (Lexer h) >>= f = Lexer $ \inStr ->
        let (msg, pos, str, x) = h inStr
            (Lexer g) = f x
            (msg', pos', str', x') = g (pos, str)
        in  (msg ++ msg', pos', str', x')

-- Function
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
        | otherwise -> ([Message (Ident pos [x]) "不明な文字です"], nextChar pos, xs, Nothing)
        where
        procAll:: (String -> Token) -> (Char -> Bool) -> ([Message], Position, String, Maybe PosToken)
        procAll cstr cond = ([], newPos, rest, Just $ PosToken pos $ cstr (x:chars)) where
            newPos = stepChar pos $ length chars
            (chars, rest) = span cond xs
        procQuote:: (String -> Token) -> (Char -> Bool) -> ([Message], Position, String, Maybe PosToken)
        procQuote cstr cond = case span cond xs of
            (chars, _:rest) -> ([], stepChar pos $ length chars, rest, Just $ PosToken pos $ cstr chars)
            (chars, _) -> ([Message (Ident pos []) "終わりの引用符がありません"], pos, [], Just $ PosToken pos $ cstr chars)
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