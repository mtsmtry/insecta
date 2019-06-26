module Parser.Data(
    module Parser.Data,
    module Common.Data
) where

import Common.Data
import qualified Data.Map as M

-- Lexial Data
data PosToken = PosToken Position Token deriving (Show)

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

-- Program
data DeclaBody = DeclaBody [IdentWith Statement] Expr deriving (Show)

data Decla =  AxiomDecla [[VarDec]] DeclaBody 
            | TheoremDecla [[VarDec]] DeclaBody [IdentWith Statement]
            | DefineDecla Ident [[VarDec]] Expr DeclaBody
            | PredicateDecla Ident [[VarDec]] Ident Expr DeclaBody
            | DataTypeDecla Ident Expr
            | UndefDecla Ident Expr (Maybe EmbString)
            | InfixDecla Bool Int Int Ident deriving (Show)

data TypingKind = NormalTyping | ExtendTyping deriving (Eq, Show)

data VarDec = VarDec { varDecKind::TypingKind, varDecId::Ident, varDecTy::Expr } deriving (Show)
data QtfVarDec = QtfVarDec Quantifier VarDec deriving (Show)
data VarDecSet = VarDecSet [Ident] TypingKind Expr deriving (Show)

type IdentWith a = (Ident, a)

data Command = StepCmd | ImplCmd | UnfoldCmd | FoldCmd | TargetCmd | InsertCmd | BeginCmd | WrongCmd deriving (Eq, Show)

data Statement = CmdStm (IdentWith Command) Expr
    | AssumeStm (IdentWith Command) Expr [IdentWith Statement]
    | ForkStm [[IdentWith Statement]]
    | VarDecStm [QtfVarDec] deriving (Show)