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
showToken Comma = ","
showToken ParenOpen = "("
showToken ParenClose = ")"

data Ident = Ident { idPos::Position, idStr::String } deriving (Show)
instance Eq Ident where
    a == b = idStr a == idStr b

data IdentInt = IdentInt { idNumPos::Position, idNum::Int } deriving (Show)
instance Eq IdentInt where
    a == b = idNum a == idNum b

data EmbPart = EmbVar Int | EmbStr String deriving (Show)
type EmbString = [EmbPart]

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
data FunAttr = OFun | CFun | AFun | ACFun String deriving (Eq, Show)

data Fom = FunTypeFom { funTypeIdent::Ident, funArgTypes::[Fom], funRetType::Fom }
    | PredFom { predVl::Fom, predTy::Fom }
    | FunFom { funAttr::FunAttr, funName::Ident, funType::Fom, funArgs::[Fom] } 
    | CstFom { cstName::Ident, cstType::Fom }
    | VarFom { varName::Ident, varType::Fom }
    | StrFom Ident
    | NumFom IdentInt
    | Rewrite { rewReason::Reason, rewLater::Fom, rewOlder::Fom }
    | UnknownFom
    | TypeOfType deriving (Show)

data Reason = NormalReason Rule AssignMap 
    | UnfoldReason Entity AssignMap
    | EqualReason 
    | SortReason deriving (Show)

instance Eq Reason where
    a == b = False

makeBinary:: String -> Fom -> Fom -> Fom
makeBinary str a b = FunFom OFun (Ident NonePosition str) propType [a, b]

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
latestFom fom@Rewrite{} = latestFom $ rewLater fom
latestFom fom = fom 

oldestFom:: Fom -> Fom
oldestFom fom@Rewrite{} = oldestFom $ rewOlder fom
oldestFom fom = fom

applyArgs:: (Fom -> Fom) -> Fom -> Fom
applyArgs apply fun@FunFom{} = fun{funArgs=map apply $ funArgs fun}
applyArgs apply fom = apply fom

applyArgsOnce:: (Fom -> Maybe Fom) -> Fom -> Maybe Fom
applyArgsOnce apply fun@FunFom{} = do
    args <- applyOnce (funArgs fun) []
    return fun{funArgs=args}
    where
    applyOnce:: [Fom] -> [Fom] -> Maybe [Fom]
    applyOnce [] _ = Nothing
    applyOnce (a:as) as' = maybe (applyOnce as (a:as')) (\x-> Just $ reverse (x:as') ++ as) (apply a)

-- Rewriting
data RuleKind = SimpRule | ImplRule | EqualRule deriving (Eq, Show)
data PredRule = PredRule { predRuleTrg::Fom, predRulePredName::String, predRuleTrgLabel::String, predRuleTy::Fom }
data Rule = Rule{ ruleKind::RuleKind, ruleIdent::Ident, ruleProof::Maybe Proof, ruleLabel::String, ruleBf::Fom, ruleAf::Fom } deriving (Show)
type AssignMap = M.Map String Fom
type RuleMap = M.Map String [Rule]
type PredRuleMap = M.Map String (M.Map String [PredRule])

insertPredRuleToMap:: PredRule -> PredRuleMap -> PredRuleMap
insertPredRuleToMap rule = M.alter updatePredMap (predRulePredName rule) where
    updatePredMap map = Just $ maybe M.empty (M.alter updateTrgList $ predRuleTrgLabel rule) map
    updateTrgList list = Just $ maybe [rule] (rule:) list

insertRuleToMap:: Rule -> RuleMap -> RuleMap
insertRuleToMap rule = M.alter updateList (ruleLabel rule) where
    updateList list = Just $ maybe [rule] (rule:) list

-- Program
data Decla = Axiom [VarDec] Expr 
    | Theorem [VarDec] Expr [IdentWith Statement]
    | Define Ident [VarDec] Expr Expr
    | Predicate Ident Ident Expr [VarDec] Expr
    | DataType Ident Expr 
    | Undef Ident Expr (Maybe EmbString)
    | InfixDecla Bool Int Int Ident deriving (Show)

type VarDec = [(Ident, Expr)]
data VarDecSet = VarDecSet [Ident] Expr deriving (Show)

data Entity = Entity { entName::String, entType::Fom, entConst::Bool, entLatex::Maybe EmbString, entFunAttr::FunAttr, entDef::Maybe Fom }
    | PredEntity { predSelf::String, predExtend::Fom, predDef::Fom, predName::String }  deriving (Show)
    
type IdentWith a = (Ident, a)

data Command = StepCmd | ImplCmd | UnfoldCmd | TargetCmd | BeginCmd | WrongCmd deriving (Eq, Show)
-- data IdentCmd = IdentCmd Ident Command deriving (Show)
-- data IdentStm = IdentStm { identStmId::Ident, identStmStm::Statement } deriving (Show)
data Statement = CmdStm (IdentWith Command) Expr
    | AssumeStm (IdentWith Command) Expr [IdentWith Statement]
    | ForkStm [(IdentWith Command, [IdentWith Statement])]
    | ExistsStm Ident [Ident] Expr
    | ForAllStm Ident Expr deriving (Show)

data StrategyOrigin = StrategyOriginAuto | StrategyOriginWhole | StrategyOriginLeft | StrategyOriginFom Fom | StrategyOriginContext Fom | StrategyOriginWrong deriving (Show)
data StrategyOriginIdent = StrategyOriginIdent Ident StrategyOrigin deriving (Show)
data StrategyRewrite = CmdRewrite Command Fom | AssumeRewrite Command Fom Strategy | ForkRewrite [(Command, Strategy)] | WrongRewrite deriving (Show)
data Strategy = Strategy StrategyOriginIdent [StrategyRewrite] deriving (Show)

data ProofCommand = ProofCommand { prfCmdCmd::Command, prfCmdRewrite::Fom } deriving (Show)
data ProofProcess = CmdProcess ProofCommand | AssumeProcess ProofCommand Fom Proof | ForkProcess [(ProofCommand, Proof)] | WrongProcess deriving (Show)
data ProofOrigin = ProofOriginContext [(Entity, Fom)] | ProofOriginFom Fom | ProofOriginLeft Fom | ProofOriginWrong deriving (Show)
data Proof = Proof { prfOrigin::ProofOrigin, prfProcesses::[ProofProcess], prfBegin::Fom, prfEnd::Fom } deriving (Show)

data Quantifier = ForAll | Exists [Ident] deriving (Show)
data Variable = Variable Quantifier Fom deriving (Show)
type VarMap = M.Map String Variable

-- Context
type Simplicity = [String] -- functions ordered by simplicity
type EntityMap = M.Map String Entity
type LatexMap = M.Map String Fom

data Context = Context { 
    conVar::VarMap,
    conOpe::OpeMap,
    conList::Simplicity,
    conSimp::RuleMap, 
    conImpl::RuleMap,
    conEnt::EntityMap,
    conPred::PredRuleMap }

newContext:: OpeMap -> Context
newContext omap = Context {
        conVar=M.empty,
        conOpe=omap,
        conList=[],
        conSimp=M.empty, 
        conImpl=M.empty,
        conEnt=buildInScope,
        conPred=M.empty }
    where
    buildInEnt name = Entity { entName=name, entType=TypeOfType, entConst=True, entLatex=Nothing, entFunAttr=OFun, entDef=Nothing }
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

updateFunAttr:: String -> (FunAttr -> FunAttr) -> Analyzer ()
updateFunAttr name f = updateEnt $ M.adjust (\ent-> ent{entFunAttr=f $ entFunAttr ent}) name
    
insertEnt:: Bool -> Ident -> Fom -> Analyzer ()
insertEnt const id ty = updateEnt $ M.insert (idStr id) 
    (Entity { entName=show id, entType=ty, entConst=const, entLatex=Nothing, entFunAttr=OFun, entDef=Nothing })

insertEntWithDef:: Bool -> Ident -> Fom -> Fom -> Analyzer ()
insertEntWithDef const id ty def = updateEnt $ M.insert (idStr id) 
    (Entity { entName=show id, entType=ty, entConst=const, entLatex=Nothing, entFunAttr=OFun, entDef=Just def })

insertEntWithLatex:: Bool -> Ident -> Fom -> Maybe EmbString -> Analyzer ()
insertEntWithLatex const id ty latex = updateEnt $ M.insert (idStr id) 
    (Entity { entName=show id, entType=ty, entConst=const, entLatex=latex, entFunAttr=OFun, entDef=Nothing })

lookupEnt:: String -> Analyzer (Maybe Entity)
lookupEnt str = do
    emap <- fmap conEnt getContext
    return $ M.lookup str emap

lookupPredRules:: String -> String -> Analyzer [PredRule]
lookupPredRules pred trg = do
    rmap <- fmap conPred getContext
    return $ fromMaybe [] $ M.lookup pred rmap >>= M.lookup trg