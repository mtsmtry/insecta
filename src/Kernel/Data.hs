module Kernel.Data(
    module Kernel.Data, 
    module Common.Data
) where
import Common.Data
import Common.Utility
import qualified Data.Map as M

-- Formula elements 
data FunAttr = OFun | CFun | AFun | ACFun deriving (Eq, Show)
newtype Ident = Ident String deriving (Eq, Ord, Show)
newtype Natural = Natural Int deriving (Eq, Ord, Show)

-- Formulas
data AtomFom = 
      StrFom String
    | NatFom Natural
    | SubTypeFom Fom
    | TypeOfType 
    | UnknownFom deriving (Eq)

data StructFom ele =
      VarFom { varFomId::Ident, varFomTy::ele }
    | FunFom { funAttr::FunAttr, funId::Ident, funTy::Fom, funArgs::[ele] }
    | LambdaFom { lambdaTy::ele, lambdaArgs::[Ident], lambdaBody::ele }
    | FunTyFom { funTyId::Ident, funArgTys::[Fom], funRetTy::Fom }
    | PredTyFom { predTyName::Ident, predTyArgs::[ele], predTyBase::ele }
    | PredFom { predVl::ele, predTy::ele }
    | AtomFom AtomFom

instance Eq ele => Eq (StructFom ele) where
  a@FunFom{} == b@FunFom{} = sameAttr && case (funAttr a, funAttr b) of
          (ACFun, _) -> equalACFun a b
          (_, ACFun) -> equalACFun a b
          _ -> funArgs a == funArgs b
      where
      sameAttr:: Bool
      sameAttr = funId a == funId b && funTy a == funTy b
      equalACFun:: Eq fom => StructFom fom -> StructFom fom -> Bool
      equalACFun a b = equalAsSet (funArgs a) (funArgs b) where
  (PredFom vl ty) == (PredFom vl' ty') = vl == vl' && ty == ty'
  (PredTyFom id args _) == (PredTyFom id' args' _) = id == id' && args == args'
  (FunTyFom id args ret) == (FunTyFom id' args' ret') = id == id' && args == args' && ret == ret'
  (AtomFom a) == (AtomFom b) = a == b
  a == b = False

newtype Fom = Fom (StructFom Fom) deriving (Eq)
typeFom:: Fom
typeFom = Fom $ AtomFom TypeOfType

data UnaryLambda = UnaryLambda { unaryLambdaArg::Ident, unaryLambdaBody::PtnFom }
data PtnFom = 
      PtnFom { fromPtn:: StructFom PtnFom }
    | Placeholder { phIdent::Ident, phType::Fom }
    | RawVarFom Fom
    | ACInsertFom { acInsert::Ident, acInsertFun::PtnFom }
    | ACRestFom { acRest::Ident, acFun::PtnFom }
    | ACEachFom { acEachList::Ident, acEachSrcFun::Ident, acEachFun::Fom, acEachLambda::UnaryLambda }

data RewFom = 
      RewFom { fromRew::StructFom RewFom }
    | Rewrite { rewReason::Reason, rewLater::RewFom, rewOlder::RewFom }

-- Types for rewriting
data QtfVariable = QtfVariable Quantifier Variable
data Variable = Variable { varName::Ident, varTy::Fom }
data Define = Define { defScope::SymbolMap, defBody::Fom, defArgs::[Variable] }
data Symbol = Symbol { symName::String, symDef::Maybe Define, symTy::Fom }
type SymbolMap = M.Map Ident Symbol

type AssignMap = M.Map Ident Fom
data RuleKind = SimpRule | ImplRule | EqualRule | TypingRule
data Rule = Rule { rulePtn::Fom, ruleNew::Fom, ruleKind::RuleKind }
type RuleMap = M.Map String Rule

data Reason = 
      NormalReason Rule AssignMap
    | UnfoldReason Symbol AssignMap
    | EqualReason
    | ACNormalizeReason

-- Analyzer
newtype Analyzer ctx res = Analyzer { analyze::ctx -> ([Message], res) }

instance Functor (Analyzer ctx) where
    fmap f (Analyzer g) = Analyzer $ \ctx -> let (msg, x) = g ctx in (msg, f x) 

instance Applicative (Analyzer ctx) where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad (Analyzer ctx) where
    return x = Analyzer $ const ([], x)
    (Analyzer h) >>= f = Analyzer $ \ctx -> 
        let (msg, x) = h ctx
            (msg', x') = analyze (f x) ctx
        in  (msg ++ msg', x')

type ProofAnalyzer = Analyzer ProofContext
type Simplicity = [String] -- functions ordered by simplicity
data ProofContext = ProofContext { conList::Simplicity, conSimp::RuleMap, conImpl::RuleMap, conPred::RuleMap }

data SymbolContext = SymbolContext { conSym::SymbolMap }
type SymbolAnalyzer = Analyzer SymbolContext

type AllAnalyzer = Analyzer (SymbolContext, ProofContext)