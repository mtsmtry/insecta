module Analyzer.Data(
    module Analyzer.Data,
    -- module Kernel.Data
) where
import Common.Data
-- import Kernel.Data
import qualified Data.Map as M


symbolAnalyze:: SymbolAnalyzer -> AllAnalyzer
symbolAnalyze f = Analyzer $ \(ctx, _)-> analyze f ctx
proofAnalyze:: SymbolAnalyzer -> AllAnalyzer
proofAnalyze f = Analyzer $ \(_, ctx)-> analyze f ctx


analyzeErrorM:: Ident -> String -> Analyzer (Maybe a)
analyzeErrorM ps str = Analyzer ([Message ps str], , Nothing)
analyzeErrorB:: Ident -> String -> Analyzer Bool
analyzeErrorB ps str = Analyzer ([Message ps str], , False)
analyzeError:: Ident -> String -> Analyzer ()
analyzeError ps str = Analyzer ([Message ps str], , ())

updateFunAttr:: String -> (FunAttr -> FunAttr) -> Analyzer ()
updateFunAttr name f = updateEnt $ map $ M.adjust (\ent-> ent{entFunAttr=f $ entFunAttr ent}) name

-- Strategy
data StrategyOrigin =     StrategyOriginAuto 
                        | StrategyOriginWhole 
                        | StrategyOriginLeft 
                        | StrategyOriginFom Fom 
                        | StrategyOriginContext Fom 
                        | StrategyOriginWrong          

data StrategyRewrite =    CmdRewrite Command Fom 
                        | AssumeRewrite Command Fom Strategy 
                        | ForkRewrite [(Command, Strategy)] 
                        | InsertRewrite Fom 
                        | WrongRewrite

data StrategyOriginIdent = StrategyOriginIdent Ident StrategyOrigin 

data Strategy = Strategy StrategyOriginIdent [StrategyRewrite]


instance Eq Quantifier where
    ForAll == ForAll = True
    (Exists as) == (Exists bs) = equalAsSet as bs
    _ == _ = False


data Entity2 = Entity2 { 
    ent2Name::Ident,
    ent2Type::Fom,
    ent2Latex::Maybe EmbString,
    ent2FunAttr::FunAttr,
    ent2Qtf::Quantifier,
    ent2Def::Maybe Define,
    ent2Pred::Maybe Variable } deriving (Show)


type AxiomSetKey = Int
type AxiomSet = [Axiom]

data Theorem = Theorem { thmRule::Rule, thmProof::Proof }

data SymbolSystem = SymbolSystem { symDependSyms::[SymbolSystem], symUndefs::[Undef], symAxioms::[Axiom], symDefines::[Define] }
data ProofSystem = ProofSystem { prfDependPrfs::[ProofSystem], prfDependSyms::[SymbolSystem], prfTheorems::[Theorem] }




-- Context
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
