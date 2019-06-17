module Parser.Declaration where
import Parser.Data
import Parser.Combinater
import Parser.Expression
import qualified Data.Map as M

parseCommaSeparated:: Parser (Maybe a) -> Parser [a]
parseCommaSeparated = parseSeparated $ parseToken Comma

parseTypingKind:: Parser (Maybe TypingKind)
parseTypingKind = do
    sem <- parseSymbol ":"
    if isNothing sem then return Nothing else do
        ope <- parseToken (OperatorToken ">")
        return $ Just $ if isNothing ope then NormalTyping else ExtendTyping

parseMultiLineStm:: OpeMap -> Parser (Maybe [IdentWith Statement])
parseMultiLineStm omap = Just <$> parseSequence (parseStatement omap)

parseStatement:: OpeMap -> Parser (Maybe (IdentWith Statement))
parseStatement omap = parseCmd >>= \case
        Just idCmd -> withIdent (fst idCmd) $ parseSwitch (switch idCmd) (other idCmd)
        Nothing -> parseIdent `rollback` \keyword-> withIdent keyword $ case idStr keyword of
            "forall" -> return (Just VarDecStm) <++> parseForAllVarDecs omap
            "exists" -> return (Just VarDecStm) <++> parseExistsVarDecs omap
            "fork" -> return (Just (\x xs-> ForkStm (x:xs))) <++> parseBlock <&&> parseSequence parseFork
                where parseFork = return (Just id) <::> parseToken (IdentToken "fork") <++> parseBlock
            _ -> return Nothing
    where
    switch idCmd = \case
        "assume" -> Just $ return (Just $ AssumeStm idCmd) <++> parseExpr omap <++> parseBlock
        _ -> Nothing
    other idCmd = return (Just $ CmdStm idCmd) <++> parseExpr omap
    parseCmd:: Parser (Maybe (IdentWith Command))
    parseCmd = parseIdent `rollback` (\id@(Ident _ str)-> (return . (\case WrongCmd-> Nothing; cmd-> Just (id, cmd)) . cmdCase) str)
        where cmdCase = \case "step" -> StepCmd; "impl"  -> ImplCmd;  "unfold" -> UnfoldCmd; "insert" -> InsertCmd;
                              "fold" -> FoldCmd; "begin" -> BeginCmd; "target" -> TargetCmd; _ -> WrongCmd
    parseBlock:: Parser (Maybe [IdentWith Statement])
    parseBlock = return (Just id) <::> parseSymbol "{" <&&> parseSequence (parseStatement omap) <::> parseSymbol "}"
    withIdent:: Ident -> Parser (Maybe a) -> Parser (Maybe (IdentWith a))
    withIdent id parse = parse >>= \case
        Just item -> return $ Just (id, item)
        Nothing -> return Nothing

parseVarDecs:: OpeMap -> Parser (Maybe [VarDec])
parseVarDecs omap = fmap (Just . conv) parse where
    parse:: Parser [VarDecSet]
    parse = parseCommaSeparated $ parseVarDecSet omap
    conv:: [VarDecSet] -> [VarDec]
    conv = map make . concatMap (uncurry zip . toTuple)
    make (name, (kind, ty)) = VarDec kind name ty
    toTuple (VarDecSet names kind ty) = (names, repeat (kind, ty))
    parseVarDecSet:: OpeMap -> Parser (Maybe VarDecSet)
    parseVarDecSet omap = return (Just VarDecSet) <&&> parseCommaSeparated parseIdent <++> parseTypingKind <++> parseExpr omap
parseParenVarDecs omap = return (Just id) <::> parseToken ParenOpen <++> parseVarDecs omap <::> parseToken ParenClose
parseParenVarDecsSet omap = fmap Just $ parseSequence $ parseParenVarDecs omap

parseForAllVarDecs:: OpeMap -> Parser (Maybe [QtfVarDec])
parseForAllVarDecs omap = return (Just (map (QtfVarDec ForAll))) <++> parseVarDecs omap

parseExistsVarDecs:: OpeMap -> Parser (Maybe [QtfVarDec])
parseExistsVarDecs omap = leastOne <$> parseCommaSeparated (parseExistsVarDec omap) where
    leastOne:: [a] -> Maybe [a]
    leastOne decs = if null decs then Nothing else Just decs
    existsVarDec:: Ident -> [Ident] -> Expr -> QtfVarDec
    existsVarDec id refs ty = QtfVarDec (Exists refs) $ VarDec NormalTyping id ty
    parseExistsVarDec:: OpeMap -> Parser (Maybe QtfVarDec)
    parseExistsVarDec omap = return (Just existsVarDec) <++> parseIdent 
        <::> parseSymbol "[" <&&> parseCommaSeparated parseIdent <::> parseSymbol "]" <::> parseSymbol ":" <++> parseExpr omap 

parseLatex:: Parser (Maybe EmbString)
parseLatex = return (Just id) <::> parseToken (IdentToken "latex") <++> parseEmbString

parseDecla:: OpeMap -> Parser (Maybe Decla)
parseDecla omap = parseIdent >>= \case
    Just (Ident _ x)-> parseDecla omap x
    Nothing -> return Nothing
    where
    parseDeclaBody:: OpeMap -> Parser (Maybe DeclaBody)
    parseDeclaBody omap = return (Just DeclaBody) <&&> parseSequence (parseStatement omap) <++> parseExpr omap
    parseDecla:: OpeMap -> String -> Parser (Maybe Decla)
    parseDecla omap "axiom" = return (Just AxiomDecla) <++> parseParenVarDecsSet omap
        <::> parseSymbol "{" <++> parseDeclaBody omap <::> parseSymbol "}"
    parseDecla omap "theorem" = return (Just TheoremDecla) <++> parseParenVarDecsSet omap
        <::> parseSymbol "{" <++> parseDeclaBody omap
        <::> parseToken (IdentToken "proof") <::> parseSymbol ":" <++> parseMultiLineStm omap <::> parseSymbol "}"
    parseDecla omap "def" = return (Just DefineDecla) <++> parseIdent <++> parseParenVarDecsSet omap
        <::> parseSymbol ":" <++> parseExpr omap
        <::> parseSymbol "{" <++> parseDeclaBody omap <::> parseSymbol "}"
    parseDecla omap "pred" = return (Just PredicateDecla) <++> parseIdent <++> parseParenVarDecsSet omap
        <::> parseSymbol "[" <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap <::> parseSymbol "]"
        <::> parseSymbol "{" <++> parseDeclaBody omap <::> parseSymbol "}"
    parseDecla omap "data" = return (Just DataTypeDecla)
        <++> parseIdent <::> parseOperator "=" <++> parseExpr omap
    parseDecla omap "undef" = return (Just UndefDecla) <++> parseIdent <::> parseSymbol ":" <++> parseExpr omap <!!> parseLatex
    parseDecla omap "infixl" = return (Just (InfixDecla True  2)) <++> parseNumber <++> parseAnyOperator
    parseDecla omap "infixr" = return (Just (InfixDecla False 2)) <++> parseNumber <++> parseAnyOperator 
    parseDecla omap "unaryl" = return (Just (InfixDecla True  1)) <++> parseNumber <++> parseAnyOperator
    parseDecla omap "unaryr" = return (Just (InfixDecla False 1)) <++> parseNumber <++> parseAnyOperator
    parseDecla _ _ = return Nothing