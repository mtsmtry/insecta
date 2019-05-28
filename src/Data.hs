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

-- Lexer Monad
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

-- Parser Monad
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

-- Analyzer Monad
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

-- Lexial Data
data Position = Position Int Int | NonePosition deriving (Show)
initialPosition = Position 1 1
stepChar (Position l c) n = Position l (c+n)
nextChar (Position l c) = Position l (c+1)
nextLine (Position l c) = Position (l+1) 1

data PosToken = PosToken Position Token deriving (Show)

data Message = Message Ident String
instance Show Message where
    show (Message id str) = "(" ++ show (idPos id) ++ ") " ++ str

type OpeMap = M.Map String (Int, Int, Bool) -- (argument number, preceed, is left associative)

-- Token
data Token = IdentToken String 
    | NumberToken Int 
    | StringToken String 
    | CharToken Char
    | SymbolToken String 
    | OperatorToken String
    | Comma
    | ParenOpen
    | ParenClose
    | EndToken deriving (Eq, Show)

showToken:: Token -> String
showToken (SymbolToken s) = s
showToken (OperatorToken s) = s
showToken (IdentToken s) = s
showToken (NumberToken n) = show n
showToken (StringToken s) = '"':s ++ "\""
showToken (CharToken s) = ['\'', s, '\'']
showToken Comma = ","
showToken ParenOpen = "("
showToken ParenClose = ")"

data Ident = Ident { idPos::Position, idStr::String } deriving (Show)
instance Eq Ident where
    a == b = idStr a == idStr b

data IdentInt = IdentInt { idNumPos::Position, idNum::Int } deriving (Show)
instance Eq IdentInt where
    a == b = idNum a == idNum b

-- Expression
data Expr = IdentExpr Ident
    | FunExpr Ident [Expr]
    | StringExpr Ident
    | NumberExpr IdentInt deriving (Show)

-- Formula
data Formula = Formula { fomBody::FormulaBody, evalType::Formula }
    | TypeOfType 
    | Rewrite { reason::Reason, later::Formula, older::Formula } deriving (Eq, Show)

data FunType = OFun | CFun | ACFun String deriving (Eq, Show)

data FormulaBody = FunTypeFormula { funTypeName::Ident, funArgTypes::[Formula], funRetType::Formula }
    | FunFormula { funType::FunType, funName::Ident, funArgs::[Formula] } 
    | CstFormula Ident
    | VarFormula Ident
    | StrFormula Ident
    | NumFormula Int deriving (Eq, Show)

data Reason = StepReason Rule AssignMap 
    | ImplReason Rule AssignMap 
    | EqualReason deriving (Eq, Show)

makeTypeFormula:: String -> Formula
makeTypeFormula str = Formula (CstFormula $ Ident NonePosition str) TypeOfType

latestFormula:: Formula -> Formula
latestFormula fom@Rewrite{} = later fom
latestFormula fom = fom 

oldestFormula:: Formula -> Formula
oldestFormula fom@Rewrite{} = older fom
oldestFormula fom = fom

applyArgs:: (Formula -> Formula) -> Formula -> Formula
applyArgs apply fom = applyArgs fom where
    applyArgs:: Formula -> Formula
    applyArgs (Formula fun@FunFormula{} etype) = Formula fun{funArgs=map apply $ funArgs fun} etype
    applyArgs _ = apply fom

funIdent:: Formula -> Maybe Ident
funIdent fom@Formula{} = funBodyIdent $ fomBody fom where
    funBodyIdent:: FormulaBody -> Maybe Ident
    funBodyIdent fun@FunTypeFormula{} = Just $ funName fun
    funBodyIdent _ = Nothing

changeArgs:: Formula -> [Formula] -> Formula
changeArgs (Formula (FunFormula ftype id _) etype) args = (Formula (FunFormula ftype id args) etype)

-- Rewriting
type Rule = (Formula, Formula)
type AssignMap = M.Map String Formula

-- Program
data Statement = SingleStm Command Expr
    | BlockStm [Statement]
    | AssumeStm Command Expr Expr Statement
    | ForkStm [Statement] deriving (Show)

data Decla = Axiom [VarDec] Expr 
    | Theorem [VarDec] Expr Statement
    | Define Ident [VarDec] Expr Expr
    | Predicate Ident Ident Expr [VarDec] Expr
    | DataType Ident Expr 
    | Undef Ident Expr (Maybe Expr)
    | InfixDecla Bool Int Int Ident deriving (Show)

type VarDec = [(Ident, Expr)]
data VarDecSet = VarDecSet [Ident] Expr deriving (Show)
data Command = StepCmd | ImplCmd | UnfoldCmd | WrongCmd String deriving (Show)

data Entity = Entity { entName::String, entType::Formula, entConst::Bool, entLatex::String } deriving (Show)
    
-- Context
type RuleMap = M.Map String [Rule]
type Simplicity = [String] -- functions ordered by simplicity
type EntityMap = M.Map String Entity
type LatexMap = M.Map String Formula
type PredicateMap = M.Map String Formula

data Context = Context { 
    conOpe::OpeMap,
    conList::Simplicity,
    conSimp::RuleMap, 
    conImpl::RuleMap,
    conPred::PredicateMap,
    conEnt::EntityMap }
    
newContext:: OpeMap -> Context
newContext omap = Context { 
        conOpe=omap,
        conList=[],
        conSimp=M.empty, 
        conImpl=M.empty,
        conPred=M.empty,
        conEnt=buildInScope }
    where
    buildInEnt name = Entity { entName=name, entType=TypeOfType, entConst=True, entLatex="" }
    buildInTypes = ["Prop", "Char", "Type"]
    buildInScope = M.fromList $ map (\name-> (name, buildInEnt name)) buildInTypes

-- Context Monad
updateContext selector f = Analyzer $ ([], , ()) . f
updateList f = Analyzer $ \ctx-> ([], ctx{conList=f $ conList ctx}, ())
updateSimp f = Analyzer $ \ctx-> ([], ctx{conSimp=f $ conSimp ctx}, ())
updateImpl f = Analyzer $ \ctx-> ([], ctx{conImpl=f $ conImpl ctx}, ())
updateEnt f = Analyzer $ \ctx-> ([], ctx{conEnt=f $ conEnt ctx}, ())

onContext:: (Context -> c) -> (c -> b -> a) -> b -> Analyzer a
onContext selector f trg = do
    omap <- fmap selector getContext
    return $ f omap trg

getContext:: Analyzer Context
getContext = Analyzer $ \ctx -> ([], ctx, ctx)

onOpeMap:: (OpeMap -> b -> a) -> b -> Analyzer a
onOpeMap = onContext conOpe

analyzeErrorM:: Ident -> String -> Analyzer (Maybe a)
analyzeErrorM ps str = Analyzer ([Message ps str], , Nothing)
analyzeErrorB:: Ident -> String -> Analyzer Bool
analyzeErrorB ps str = Analyzer ([Message ps str], , False)
analyzeError:: Ident -> String -> Analyzer ()
analyzeError ps str = Analyzer ([Message ps str], , ())

-- Context Accesser
insertEnt:: Bool -> Ident -> Formula -> Analyzer ()
insertEnt const id _type = updateEnt $ M.insert (show id) 
    (Entity { entName=show id, entType=_type, entConst=const, entLatex="" })

lookupEnt:: String -> Analyzer (Maybe Entity)
lookupEnt str = do
    emap <- fmap conEnt getContext
    return $ M.lookup str emap