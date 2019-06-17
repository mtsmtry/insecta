module Parser.Function(parseProgram, parseExprs) where
import Parser.Data
import Parser.Expression
import Parser.Declaration
import Parser.Combinater

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