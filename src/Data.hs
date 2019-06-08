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
import Library

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

rollback:: Parser (Maybe a) -> (a -> Parser (Maybe b)) -> Parser (Maybe b)
rollback (Parser first) second = Parser $ \ts -> case first ts of
    (msg1, ts1, Just res1) -> let (Parser g) = second res1 in case g ts1 of
        all@(msg2, ts2, Just res2) -> (msg1 ++ msg2, ts2, Just res2)
        _ -> ([], ts, Nothing)
    _ -> ([], ts, Nothing)

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

data Operator = Operator { opeArgNum::Int, opePreceed::Int, opeLeftAssoc::Bool }
type OpeMap = M.Map String Operator
defaultOpe = Operator { opeArgNum=2, opePreceed= -1, opeLeftAssoc=True }

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
data UnaryLambda = UnaryLambda { unaryLambdaArg::String, unaryLambdaBody::Fom } deriving (Show)

data FunAttr = OFun | CFun | AFun | ACFun deriving (Eq, Show)

data Fom = FunTypeFom { funTypeIdent::Ident, funArgTypes::[Fom], funRetType::Fom }
    | PredTypeFom { predTyName::Ident, predTyArgs::[Fom] }
    | PredFom { predVl::Fom, predTy::Fom }
    | FunFom { funAttr::FunAttr, funName::Ident, funType::Fom, funArgs::[Fom] }
    | CstFom { cstName::Ident, cstType::Fom }
    | VarFom { varName::Ident, varType::Fom }
    | LambdaFom { lambdaType::Fom, lambdaArgs::[String], lambdaBody::Fom }
    | StrFom Ident
    | NumFom IdentInt
    | Rewrite { rewReason::Reason, rewLater::Fom, rewOlder::Fom }
    | ACInsertFom { acInsert::String, acInsertFun::Fom }
    | ACRestFom { acRest::String, acFun::Fom }
    | ACEachFom { acEachList::String, acEachSrcFun::String, acEachFun::Fom, acEachLambda::UnaryLambda }
    | SubTypeFom Fom
    | ListFom [Fom]
    | RawVarFom Fom
    | UnknownFom
    | TypeOfType deriving (Show)

data Reason = NormalReason Rule AssignMap 
    | UnfoldReason Entity AssignMap
    | EqualReason 
    | ACNormalizeReason deriving (Show)

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
showIdent fom@PredFom{} = showIdent $ predVl fom
showIdent fom@LambdaFom{} = showIdent $ lambdaBody fom
showIdent fom@PredTypeFom{} = predTyName fom
showIdent (RawVarFom raw) = showIdent raw
showIdent UnknownFom = Ident NonePosition "unknown"
showIdent fom = error $ show fom

evalType:: Fom -> Fom
evalType (ACEachFom _ _ fun _) = evalType fun
evalType (ACRestFom _ fun) = evalType fun
evalType (ACInsertFom _ fun) = evalType fun
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
latestFom rew@Rewrite{} = latestFom $ rewLater rew
latestFom fun@FunFom{} = applyArgs latestFom fun
latestFom fom = fom

oldestFom:: Fom -> Fom
oldestFom rew@Rewrite{} = oldestFom $ rewOlder rew
oldestFom fun@FunFom{} = applyArgs oldestFom fun
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
data RuleKind = SimpRule | ImplRule | EqualRule | PredRule deriving (Eq, Show)
data Rule = Rule { 
    ruleKind::RuleKind,
    ruleIdent::Ident,
    ruleProof::Maybe Proof,
    ruleLabel::String,
    ruleBf::Fom,
    ruleAf::Fom,
    ruleProp::Fom } deriving (Show)
type AssignMap = M.Map String Fom
type RuleMap = M.Map String [Rule]
type PredRuleMap = M.Map String (M.Map String [Rule])

insertPredRuleToMap:: Rule -> PredRuleMap -> PredRuleMap
insertPredRuleToMap rule = M.alter updatePredMap (ruleLabel rule) where
    updatePredMap map = Just $ maybe M.empty (M.alter updateTrgList $ ruleLabel rule) map
    updateTrgList list = Just $ maybe [rule] (rule:) list

insertRuleToMap:: Rule -> RuleMap -> RuleMap
insertRuleToMap rule = M.alter updateList (ruleLabel rule) where
    updateList list = Just $ maybe [rule] (rule:) list

-- Program
data DefineBody = DefineBody [IdentWith Statement] Expr deriving (Show)
data Decla = AxiomDecla [[VarDec]] Expr 
    | TheoremDecla [[VarDec]] Expr [IdentWith Statement]
    | DefineDecla Ident [[VarDec]] Expr DefineBody
    | PredicateDecla Ident [[VarDec]] Ident Expr DefineBody
    | DataTypeDecla Ident Expr 
    | UndefDecla Ident Expr (Maybe EmbString)
    | InfixDecla Bool Int Int Ident deriving (Show)

data TypingKind = NormalTyping | ExtendTyping deriving (Eq, Show)
data VarDec = VarDec { varDecKind::TypingKind, varDecId::Ident, varDecTy::Expr } deriving (Show)
data VarDecSet = VarDecSet [Ident] TypingKind Expr deriving (Show)

data Define = Define { defScope::EntityMap, defBody::Fom, defArgs::[String] } deriving (Show)
data Variable = Variable { varStr::String, varTy::Fom } deriving (Show)
data Entity = Entity { entName::Ident,
    entType::Fom,
    entLatex::Maybe EmbString,
    entFunAttr::FunAttr,
    entDef::Maybe Define,
    entQtf::Quantifier,
    entPred::Maybe Variable } deriving (Show)

type IdentWith a = (Ident, a)

data Command = StepCmd | ImplCmd | UnfoldCmd | FoldCmd | TargetCmd | BeginCmd | WrongCmd deriving (Eq, Show)
data Statement = CmdStm (IdentWith Command) Expr
    | AssumeStm (IdentWith Command) Expr [IdentWith Statement]
    | ForkStm [(IdentWith Command, [IdentWith Statement])]
    | ExistsStm Ident [Ident] Expr
    | ForAllStm Ident Expr deriving (Show)

data StrategyOrigin = StrategyOriginAuto | StrategyOriginWhole | StrategyOriginLeft 
    | StrategyOriginFom Fom | StrategyOriginContext Fom | StrategyOriginWrong deriving (Show)
data StrategyOriginIdent = StrategyOriginIdent Ident StrategyOrigin deriving (Show)
data StrategyRewrite = CmdRewrite Command Fom | AssumeRewrite Command Fom Strategy | ForkRewrite [(Command, Strategy)] | WrongRewrite deriving (Show)
data Strategy = Strategy StrategyOriginIdent [StrategyRewrite] deriving (Show)

data ProofCommand = ProofCommand { prfCmdCmd::Command, prfCmdRewrite::Fom } deriving (Show)
data ProofProcess = CmdProcess ProofCommand | AssumeProcess ProofCommand Fom Proof | ForkProcess [(ProofCommand, Proof)] | WrongProcess deriving (Show)
data ProofOrigin = ProofOriginContext [(Entity, Fom)] | ProofOriginFom Fom | ProofOriginLeft Fom | ProofOriginWrong deriving (Show)
data Proof = Proof { prfOrigin::ProofOrigin, prfProcesses::[ProofProcess], prfBegin::Fom, prfEnd::Fom } deriving (Show)

-- Context
type Simplicity = [String] -- functions ordered by simplicity
data Quantifier = ForAll | Exists [Ident] deriving (Show)

instance Eq Quantifier where
    ForAll == ForAll = True
    (Exists as) == (Exists bs) = equalAsSet as bs
    _ == _ = False

type EntityMap = M.Map String Entity

data Context = Context {
    conOpe::OpeMap,
    conList::Simplicity,
    conSimp::RuleMap, 
    conImpl::RuleMap,
    conEnt::[EntityMap],
    conPred::PredRuleMap }

makeEntity:: Ident -> Fom -> Entity
makeEntity id ty = Entity { entName=id, entType=ty, entLatex=Nothing, entFunAttr=OFun, entDef=Nothing, entQtf=ForAll, entPred=Nothing }

buildInOpe = M.fromList [
    (">>=", Operator 2 0 True), 
    (":", Operator 2 0 True),
    ("->", Operator 2 1 True), 
    ("|", Operator 2 2 True), 
    (".", Operator 2 100 True)]

newContext:: OpeMap -> Context
newContext omap = Context {
        conOpe=omap,
        conList=[],
        conSimp=M.empty, 
        conImpl=M.empty,
        conEnt=[buildInScope],
        conPred=M.empty }
    where
    buildInEnt name = makeEntity (Ident NonePosition name) TypeOfType
    buildInTypes = ["Prop", "Char", "Type"]
    buildInScope = M.fromList $ map (\name-> (name, buildInEnt name)) buildInTypes

-- Context Accesser
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

getLocalEntMap:: Analyzer EntityMap
getLocalEntMap = Analyzer $ \ctx -> ([], ctx, head $ conEnt ctx)

onOpeMap:: (OpeMap -> b -> a) -> b -> Analyzer a
onOpeMap = onContext conOpe

analyzeErrorM:: Ident -> String -> Analyzer (Maybe a)
analyzeErrorM ps str = Analyzer ([Message ps str], , Nothing)
analyzeErrorB:: Ident -> String -> Analyzer Bool
analyzeErrorB ps str = Analyzer ([Message ps str], , False)
analyzeError:: Ident -> String -> Analyzer ()
analyzeError ps str = Analyzer ([Message ps str], , ())

updateFunAttr:: String -> (FunAttr -> FunAttr) -> Analyzer ()
updateFunAttr name f = updateEnt $ map $ M.adjust (\ent-> ent{entFunAttr=f $ entFunAttr ent}) name

insertEntMap:: Ident -> Fom -> (Entity -> Entity) -> Analyzer ()
insertEntMap id ty f = updateEnt $ mapHead $ M.insert (idStr id) $ f $ makeEntity id ty

mapHead:: (a -> a) -> [a] -> [a]
mapHead f [] = []
mapHead f (x:xs) = f x:xs

insertEnt:: Ident -> Fom -> Analyzer ()
insertEnt name ty = insertEntMap name ty id

subScope:: Analyzer a -> Analyzer a
subScope subRountine = do
    updateEnt (M.empty:)
    res <- subRountine
    updateEnt tail
    return res

data DeclaArea = Local | Global
lookupEntWithArea:: String -> Analyzer (Maybe (Entity, DeclaArea))
lookupEntWithArea str = do
    (local:global) <- fmap conEnt getContext
    case M.lookup str local of
        Just ent -> return $ Just (ent, Local)
        Nothing -> case mapMaybe (M.lookup str) global of
            (x:xs) -> return $ Just (x, Global)
            _ -> return Nothing

lookupEnt:: String -> Analyzer (Maybe Entity)   
lookupEnt str = do
    res <- lookupEntWithArea str
    return $ fst <$> res

lookupPredRules:: String -> String -> Analyzer [Rule]
lookupPredRules pred trg = do
    rmap <- fmap conPred getContext
    return $ fromMaybe [] $ M.lookup pred rmap >>= M.lookup trg