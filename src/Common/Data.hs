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

data Message = Message Position String
instance Show Message where
    show (Message pos str) = "(" ++ show pos ++ ") " ++ str

data EmbPart = EmbVar Int | EmbStr String deriving (Show)
type EmbString = [EmbPart]

data Quantifier = ForAll | Exists [String] deriving (Show)