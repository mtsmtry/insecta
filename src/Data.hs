module Data where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative

newtype Lexer a = Lexer { runLexer::(Position, String) -> ([Message], Position, String, a) }
newtype Parser a = Parser { runParser::[PosToken] -> ([Message], [PosToken], a) }

instance Functor Lexer where
    fmap f (Lexer g) = Lexer $ \inStr -> let (msg, pos, str, x) = g inStr in (msg, pos, str, f x)
instance Functor Parser where
    fmap f (Parser g) = Parser $ \inTok -> let (msg, tok, x) = g inTok in (msg, tok, f x)

instance Applicative Lexer where
    pure = return
    a <*> b = a >>= (<$> b)
instance Applicative Parser where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad Lexer where
    return x = Lexer $ \(pos, str) -> ([], pos, str, x)
    (Lexer h) >>= f = Lexer $ \inStr ->
        let (msg, pos, str, x) = h inStr
            (Lexer g) = f x
            (msg', pos', str', x') = g (pos, str)
        in  (msg ++ msg', pos', str', x')

instance Monad Parser where
    return x = Parser ([], , x)
    (Parser h) >>= f = Parser $ \inTok ->
        let (msg, tok, x) = h inTok
            (Parser g) = f x
            (msg', tok', x') = g tok
        in  (msg ++ msg', tok', x')

data Position = Position Int Int | NonePosition deriving (Show)
type PosStr = (Position, String)
data PosToken = PosToken Position Token deriving (Show)
data Message = Message PosStr String deriving (Show)
data Token = Ident String | Number Int | Literal String | LiteralOne Char | Symbol String | Operator String
    | Comma | ParenOpen | ParenClose | EndToken deriving (Eq, Show)

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

sameStr::PosStr -> PosStr -> Bool 
sameStr (_, a) (_, b) = a == b

makePosStr:: String -> PosStr
makePosStr s = (NonePosition, s)

makeIdentExpr:: String -> Expr
makeIdentExpr = IdentExpr . makePosStr

getPosAndStr:: Expr -> PosStr
getPosAndStr (IdentExpr ps) = ps
getPosAndStr (StringExpr ps) = ps
getPosAndStr (NumberExpr p n) = (p, show n)
getPosAndStr (Rewrite _ a _) = getPosAndStr a
getPosAndStr (FuncExpr ps _) = ps

initialPosition = Position 1 1
stepChar (Position l c) n = Position l (c+n)
nextChar (Position l c) = Position l (c+1)
nextLine (Position l c) = Position (l+1) 1

type Rule = (Expr, Expr)
type OpeMap = M.Map String (Int, Int, Bool) -- (argument number, preceed, is left associative)
type AssignMap = M.Map String Expr

type VarDec = [(PosStr, Expr)]
data VarDecSet = VarDecSet [PosStr] Expr deriving (Show)
data Command = StepCmd | ImplCmd | WrongCmd String deriving (Show)

data Expr = IdentExpr PosStr 
    | FuncExpr PosStr [Expr] 
    | StringExpr PosStr 
    | NumberExpr Position Int
    | Rewrite Reason Expr Expr deriving (Show)
data Statement = SingleStm Command Expr
    | BlockStm [Statement]
    | AssumeStm Command Expr Expr Statement
    | ForkStm [Statement] deriving (Show)
data Decla = Axiom VarDec Expr 
    | Theorem VarDec Expr Statement
    | Define PosStr VarDec Expr Expr 
    | Predicate PosStr PosStr Expr VarDec Expr
    | DataType PosStr Expr 
    | Undef PosStr Expr (Maybe Expr)
    | InfixDecla Bool Int Int PosStr deriving (Show)
data Reason = StepReason Rule AssignMap 
    | ImplReason Rule AssignMap 
    | EqualReason deriving (Show)

type RuleMap = M.Map String [Rule]
type Simplicity = [String] -- functions ordered by simplicity
type TypeMap = M.Map String Expr
type LatexMap = M.Map String Expr
type PredicateMap = M.Map String Expr
data Context = Context { ctxOMap::OpeMap, ctxTMap::TypeMap, ctxSimps::Simplicity, ctxSRule::RuleMap, ctxIRule::RuleMap, ctxLatex::LatexMap, ctxPred::PredicateMap }
newtype Analyzer a = Analyzer { analyze::Context -> ([Message], Context, a) }

instance Functor Analyzer where
    fmap f (Analyzer g) = Analyzer $ \ctx -> let (msg, ctx', x) = g ctx in (msg, ctx', f x)

instance Applicative Analyzer where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad Analyzer where
    return x = Analyzer ([], , x)
    (Analyzer h) >>= f = Analyzer $ \ts ->
        let (msg, ctx, x) = h ts
            (Analyzer g) = f x
            (msg', ctx', x') = g ctx
        in  (msg ++ msg', ctx', x')

onOpeMap:: (OpeMap -> b -> a) -> b -> Analyzer a
onOpeMap = onCtx ctxOMap

onCtx:: (Context -> c) -> (c -> b -> a) -> b -> Analyzer a
onCtx selector f trg = do
    omap <- fmap selector getContext
    return $ f omap trg

getContext:: Analyzer Context
getContext = Analyzer $ \ctx -> ([], ctx, ctx)
updateContext selector f = Analyzer $ ([], , ()) . f

updateSRule f = Analyzer $ \ctx-> ([], ctx{ctxSRule=f $ ctxSRule ctx}, ())
updateIRule f = Analyzer $ \ctx-> ([], ctx{ctxIRule=f $ ctxIRule ctx}, ())
updateSimp f = Analyzer $ \ctx-> ([], ctx{ctxSimps=f $ ctxSimps ctx}, ())
updateScope f = Analyzer $ \ctx-> ([], ctx{ctxTMap=f $ ctxTMap ctx}, ())
updateLatex f = Analyzer $ \ctx-> ([], ctx{ctxTMap=f $ ctxLatex ctx}, ())