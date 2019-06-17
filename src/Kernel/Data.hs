module Kernel.Data(
    module Kernel.Data, 
    module Common.Data
) where
import Common.Data
import qualified Data.Map as M

data FunAttr = OFun | CFun | AFun | ACFun deriving (Eq, Show)

data Fom =    FunFom        { funAttr       ::FunAttr,  funIdent    ::Ident,    funType     ::Fom, funArgs::[Fom] }
            | CstFom        { cstIdent      ::Ident,    cstType     ::Fom }
            | VarFom        { varIdent      ::Ident,    varType     ::Fom }
            | LambdaFom     { lambdaType    ::Fom,      lambdaArgs  ::[String], lambdaBody  ::Fom }
            | StrFom Ident
            | NumFom IdentInt

            | FunTypeFom    { funTypeIdent  ::Ident,    funArgTypes ::[Fom],    funRetType  ::Fom }
            | PredTypeFom   { predTyName    ::Ident,    predTyArgs  ::[Fom],    predTyBase  ::Fom }
            | PredFom       { predVl        ::Fom,      predTy      ::Fom }

            | Rewrite       { rewReason     ::Reason,   rewLater    ::Fom,      rewOlder    ::Fom }

            | ACInsertFom   { acInsert      ::String,   acInsertFun ::Fom }
            | ACRestFom     { acRest        ::String,   acFun       ::Fom }
            | ACEachFom     { acEachList    ::String,   acEachSrcFun::String,   acEachFun   ::Fom, acEachLambda::UnaryLambda }

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

data UnaryLambda = UnaryLambda { unaryLambdaArg::String, unaryLambdaBody::Fom } deriving (Show)

data ProofProcess =   CmdProcess ProofCommand 
                    | InsertProcess Fom 
                    | AssumeProcess ProofCommand Fom Proof 
                    | ForkProcess [(ProofCommand, Proof)] 
                    | WrongProcess deriving (Show)

data ProofOrigin =    ProofOriginContext [(Entity, Fom)] 
                    | ProofOriginFom Fom 
                    | ProofOriginLeft Fom 
                    | ProofOriginWrong deriving (Show)

data ProofCommand = ProofCommand { 
        prfCmdCmd::Command, 
        prfCmdRewrite::Fom } deriving (Show)

data Proof = Proof { 
        prfOrigin::ProofOrigin, 
        prfProcesses::[ProofProcess], 
        prfBegin::Fom, 
        prfEnd::Fom } deriving (Show)

makeBinary:: String -> Fom -> Fom -> Fom
makeBinary str a b = FunFom OFun (Ident NonePosition str) propType [a, b]

makeType:: String -> Fom
makeType str = CstFom{cstIdent=Ident NonePosition str, cstType=TypeOfType}

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


data Define = Define { defScope::EntityMap, defBody::Fom, defArgs::[Variable] } deriving (Show)
data Variable = Variable { varName::Ident, varTy::Fom } deriving (Show)
data QtfVariable = QtfVariable Quantifier Variable
data Entity = Entity { entName::Ident,
        entType::Fom,
        entLatex::Maybe EmbString,
        entFunAttr::FunAttr,
        entQtf::Quantifier,
        entDef::Maybe Define,
        entPred::Maybe Variable } deriving (Show)


-- Context
type Simplicity = [String] -- functions ordered by simplicity
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


data Difinition = Difinition { }
data Theory = Theory {  }
data AxiomSet = AxiomSet { axsDefs::M.Map String Dinifition }