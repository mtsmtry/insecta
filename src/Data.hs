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
    | StrExpr Ident
    | NumExpr IdentInt deriving (Show)

showExprIdent:: Expr -> Ident
showExprIdent (IdentExpr id) = id
showExprIdent (FunExpr id _) = id
showExprIdent (StrExpr id) = id
showExprIdent (NumExpr (IdentInt pos num)) = Ident pos (show num)

-- Formula
data FunAttr = OFun | CFun | ACFun String deriving (Eq, Show)

data Fom = FunTypeFom { funTypeIdent::Ident, funArgTypes::[Fom], funRetType::Fom }
    | FunFom { funAttr::FunAttr, funName::Ident, funType::Fom, funArgs::[Fom] } 
    | CstFom { cstName::Ident, cstType::Fom }
    | VarFom { varName::Ident, varType::Fom }
    | StrFom Ident
    | NumFom IdentInt
    | Rewrite { rewReason::Reason, rewLater::Fom, rewOlder::Fom }
    | TypeOfType deriving (Eq, Show)

data Reason = NormalReason Rule AssignMap 
    | EqualReason deriving (Eq, Show)

showIdent:: Fom -> Ident
showIdent fom@FunTypeFom{} = funTypeIdent fom
showIdent fom@FunFom{} = funName fom
showIdent fom@CstFom{} = cstName fom
showIdent fom@VarFom{} = varName fom
showIdent (StrFom id) = id
showIdent (NumFom (IdentInt pos num)) = Ident pos (show num)

evalType:: Fom -> Fom
evalType TypeOfType = error "evalType TypeOfType"
evalType Rewrite{} = error "evalType Rewrite{}"
evalType fom@FunFom{} = funType fom
evalType fom@CstFom{} = cstType fom
evalType fom@VarFom{} = varType fom
evalType StrFom{} = makeType "String"
evalType NumFom{} = makeType "N"
evalType FunTypeFom{} = TypeOfType

makeType:: String -> Fom
makeType str = CstFom{cstName=Ident NonePosition str, cstType=TypeOfType}

propType = makeType "Prop"

latestFom:: Fom -> Fom
latestFom fom@Rewrite{} = rewLater fom
latestFom fom = fom 

oldestFom:: Fom -> Fom
oldestFom fom@Rewrite{} = rewOlder fom
oldestFom fom = fom

applyArgs:: (Fom -> Fom) -> Fom -> Fom
applyArgs apply fun@FunFom{} = fun{funArgs=map apply $ funArgs fun}
applyArgs apply fom = apply fom

applyArgsOnce:: (Fom -> Maybe Fom) -> Fom -> Maybe Fom
applyArgsOnce apply fun@FunFom{} = do
    nargs <- applyOnce (funArgs fun) []
    return fun{funArgs=nargs}
    where
    applyOnce:: [Fom] -> [Fom] -> Maybe [Fom]
    applyOnce [] _ = Nothing
    applyOnce (a:as) as' = maybe (applyOnce as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (apply a)

-- Rewriting
data RuleKind = SimpRule | ImplRule deriving (Eq, Show)
data Rule = Rule{ ruleKind::RuleKind, ruleIdent::Ident, ruleLabel::String, ruleBf::Fom, ruleAf::Fom } deriving (Eq, Show)
type AssignMap = M.Map String Fom

-- Program
data Decla = Axiom [VarDec] Expr 
    | Theorem [VarDec] Expr [IdentStm]
    | Define Ident [VarDec] Expr Expr
    | Predicate Ident Ident Expr [VarDec] Expr
    | DataType Ident Expr 
    | Undef Ident Expr (Maybe Expr)
    | InfixDecla Bool Int Int Ident deriving (Show)

type VarDec = [(Ident, Expr)]
data VarDecSet = VarDecSet [Ident] Expr deriving (Show)
data Entity = Entity { entName::String, entType::Fom, entConst::Bool, entLatex::String } deriving (Show)
    
data Command = StepCmd | ImplCmd | UnfoldCmd | TargetCmd | BeginCmd | WrongCmd deriving (Show)
data IdentCmd = IdentCmd Ident Command deriving (Show)
data IdentStm = IdentStm { identStmId::Ident, identStmStm::Statement } deriving (Show)
data Statement = CmdStm IdentCmd Expr
    | AssumeStm IdentCmd Expr [IdentStm]
    | ForkStm [(IdentCmd, [IdentStm])]
    | ExistsStm Ident [Ident] Expr
    | ForAllStm Ident Expr deriving (Show)

data ProofCmd = StepProofCmd | ImplProofCmd | UnfoldProofCmd | WrongProofCmd
data ProofTrg = ProofTrgLeft | ProofTrgContext
data ProofOrigin = ProofOriginFom Fom | ProofOriginTrg ProofTrg | ProofOriginWrong
data ProofRewrite = CmdProof ProofCmd Fom | AssumeProof ProofCmd Fom Proof | ForkProof [(ProofCmd, Proof)] | WrongProof
data Proof = Proof ProofOrigin [ProofRewrite]
data ProofEnv = ProofEnv Proof VarMap

data Quantifier = ForAll | Exists [Ident]
data Variable = Variable Quantifier Fom
type VarMap = M.Map String Variable

-- Context
type RuleMap = M.Map String [Rule]
type Simplicity = [String] -- functions ordered by simplicity
type EntityMap = M.Map String Entity
type LatexMap = M.Map String Fom
type PredicateMap = M.Map String Fom

data Context = Context { 
    conVar::VarMap,
    conOpe::OpeMap,
    conList::Simplicity,
    conSimp::RuleMap, 
    conImpl::RuleMap,
    conPred::PredicateMap,
    conEnt::EntityMap }
    
newContext:: OpeMap -> Context
newContext omap = Context { 
        conVar=M.empty,
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

-- Context Accesser
updateContext selector f = Analyzer $ ([], , ()) . f
updateVar f = Analyzer $ \ctx-> ([], ctx{conVar=f $ conVar ctx}, ())
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

insertEnt:: Bool -> Ident -> Fom -> Analyzer ()
insertEnt const id ty = updateEnt $ M.insert (show id) 
    (Entity { entName=show id, entType=ty, entConst=const, entLatex="" })

lookupEnt:: String -> Analyzer (Maybe Entity)
lookupEnt str = do
    emap <- fmap conEnt getContext
    return $ M.lookup str emap