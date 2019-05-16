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
            [isIdentSymbol, isOperator, isBracket] = map (flip elem) ["_'" , "+-*/\\<>|?=@^$:~`.&", "(){}[],"]
            [isIdentHead, isIdentBody] = map any [[isLetter, ('_' ==)], [isLetter, isDigit, isIdentSymbol]]
                where any = F.foldr ((<*>) . (<$>) (||)) $ const False
            -- String -> Token
            toChar all = case all of [x] -> LiteralOne x; [] -> Error all "too short"; (x:xs) -> Error all "too long"
            toSymbol all = case all of "(" -> ParenOpen; ")" -> ParenClose; "," -> Comma; _ -> Symbol all

type Rule = (Expr, Expr)
type OpeMap = M.Map String (Int, Bool)
data ExprHead = ExprHead Token Int | PureExprHead Token deriving (Show, Eq)
data Expr = IdentExpr String | FuncExpr ExprHead [Expr] | StringExpr String | NumberExpr Int | Rewrite Rule Expr Expr deriving (Show, Eq)
parseExpr:: OpeMap -> State [Token] (Maybe Expr)
parseExpr omap = state $ \ts-> parseExpr ts [] [] where--4
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
    getOpe = flip M.lookup $ M.union buildInOpe omap
    buildInOpe = M.fromList [(">>=", (0, True)), ("->", (1, True))]
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
parseAnySymbol = state $ \case
    [] -> (Nothing, [])
    all@(t:ts) -> case t of Symbol _-> (Just t, ts); _-> (Nothing, all)
parseNumber = state $ \case
    [] -> (Nothing, [])
    all@(t:ts) -> case t of Number n-> (Just n, ts); _-> (Nothing, all)
parseIdent = state $ \case
    [] -> (Nothing, [])
    all@(t:ts) -> case t of Ident i-> (Just t, ts); _-> (Nothing, all)

parseSeparated:: State [Token] (Maybe s) -> State [Token] (Maybe a) -> State [Token] (Maybe [a]) 
parseSeparated s p = p >>= \case
    Just x' -> s >>= \case
        Just _ -> parseSeparated s p >>= \case
            Just r' -> return $ Just (x':r')
            Nothing -> return Nothing
        Nothing -> return $ Just [x']
    Nothing -> return $ Just []
parseCommaSeparated = parseSeparated $ parseToken Comma

data VarDecSet = VarDecSet [Token] Expr deriving (Show)
parseVarDecSet:: OpeMap -> State [Token] (Maybe VarDecSet)
parseVarDecSet omap = return (Just VarDecSet) <++> parseCommaSeparated parseIdent <::> parseSymbol ":" <++> parseExpr omap

data Statement = StepStm Expr | ImplStm Expr | AssumeStm Expr [Statement] | BlockStm String Expr [Statement] deriving (Show)
parseStatement:: OpeMap -> State [Token] (Maybe Statement)
parseStatement omap = parseIdent >>= \case
    Just (Ident "step") -> return (Just StepStm) <++> parseExpr omap
    Just (Ident "impl") -> return (Just ImplStm) <++> parseExpr omap
    Just (Ident "assume") -> return (Just AssumeStm) <++> parseExpr omap <++> parseBlock
    _ -> return Nothing 
    where parseBlock = return (Just id) <::> parseSymbol "{" <++> parseSequence (parseStatement omap) <::> parseSymbol "}"

type VarDec = [(Token, Expr)]
parseVarDecs:: OpeMap -> State [Token] (Maybe VarDec)
parseVarDecs omap = fmap conv (parseCommaSeparated $ parseVarDecSet omap) where
    toTuple (VarDecSet ns t) = (ns, repeat t)
    conv = Just . concatMap (uncurry zip) . maybe [] (map toTuple)
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose

data Decla = Axiom VarDec Expr | Theorem VarDec Expr [Statement] 
    | Define Token VarDec Expr | Predicate Token Token Expr VarDec Expr 
    | InfixDecla Bool Token Int Token deriving (Show)
parseDeclaBody:: OpeMap -> String -> State [Token] (Maybe Decla)
parseDeclaBody omap "axiom" = return (Just Axiom)
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "theorem" = return (Just Theorem) 
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" 
    <++> parseExpr omap
    <::> parseToken (Ident "proof") <::> parseSymbol ":" <++> parseSequence (parseStatement omap)
    <::> parseSymbol "}"
parseDeclaBody omap "define" = return (Just Define)
    <++> parseIdent
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "predicate" = return (Just Predicate)
    <++> parseIdent
    <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap<::> parseSymbol "]"
    <++> parseParenVarDecs omap
    <::> parseSymbol "{" <++> parseExpr omap <::> parseSymbol "}"
parseDeclaBody omap "infixl" = return (Just $ InfixDecla True)
    <++> parseAnySymbol <++> parseNumber <::> parseSymbol "=>" <++> parseIdent
parseDeclaBody omap "infixr" = return (Just $ InfixDecla False)
    <++> parseAnySymbol <++> parseNumber <::> parseSymbol "=>" <++> parseIdent
parseDeclaBody _ _ = return Nothing

parseDecla:: OpeMap -> State [Token] (Maybe Decla)
parseDecla omap = parseIdent >>= \case (Just (Ident x))-> parseDeclaBody omap x; _ -> return Nothing

parseProgram:: State [Token] ([Decla], OpeMap)
parseProgram = parseProgram' M.empty where
    parseRest:: Decla -> OpeMap -> State [Token] ([Decla], OpeMap)
    parseRest x omap = parseProgram' omap >>= \(xs, omap')-> return (x:xs, omap')
    parseProgram':: OpeMap -> State [Token] ([Decla], OpeMap)
    parseProgram' omap = parseDecla omap >>= \case
        Just x@(InfixDecla leftAssoc (Symbol s) pre fun) -> parseRest x $ M.insert s (pre, leftAssoc) omap
        Just x -> parseRest x omap
        Nothing -> return ([], omap)