module Common.Data (
    module Common.Data,
    module Data.Char,
    module Data.List,
    module Data.Maybe,
    module Data.Monoid
) where

import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid

data Position = Position Int Int | NonePosition deriving (Show)

data Message = Message Ident String
instance Show Message where
    show (Message id str) = "(" ++ show (idPos id) ++ ") " ++ str

data Ident = Ident { idPos::Position, idStr::String } deriving (Show)
instance Eq Ident where
    a == b = idStr a == idStr b

data IdentInt = IdentInt { idNumPos::Position, idNum::Int } deriving (Show)
instance Eq IdentInt where
    a == b = idNum a == idNum b

data EmbPart = EmbVar Int | EmbStr String deriving (Show)
type EmbString = [EmbPart]