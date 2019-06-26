module Prover.Data(
    module Prover.Data,
    module Kernel.Data
) where
import Kernel.Data

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