module Parser.Expression(parseExpr, parseEmbString) where
import Parser.Data
import Parser.Combinater
import qualified Data.Map as M

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
    getOpe x@(Ident pos id) = maybe ([Message x "定義されていない演算子です"], defaultOpe) ([], ) (M.lookup id omap)

    precederEq:: (Int, Bool) -> PosToken -> Bool
    precederEq _ (PosToken _ ParenOpen) = False
    precederEq _ (PosToken _ (IdentToken _)) = True
    precederEq (apre, aleft) (PosToken _ (OperatorToken t)) = aleft && ((bleft && apre <= bpre) || apre < bpre)
        where Operator _ bpre bleft = fromMaybe defaultOpe $ M.lookup t omap