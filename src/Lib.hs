module Lib
    ( someFunc
    ) where
import Data.Char
import Data.List
import Data.Maybe
import Control.Monad

data Token = EndLine | Ident String | Number Int | Literal String | LiteralOne Char | Symbol String | Error String | End deriving (Eq, Show)

pickup f [] = ([], [])
pickup f (x:xs) = if f x
    then let (token, rest) = pickup f xs in (x:token, rest) 
    else ([], x:xs)

orConds [] x = False
orConds (f:fs) x = f x || orConds fs x

getToken :: String -> (Maybe Token, String)
getToken [] = (Just End, [])
getToken (x:xs)
   | isDigit x = f (Number . read) $ pickup isDigit xs
   | isIdent x = f Ident $ pickup (orConds [isIdent, isDigit]) xs
   | isOperator x = f Symbol $ pickup isOperator xs
   | isBracket x = (Just $ Symbol [x], xs)
   | x == '"' = g Literal $ pickup (( /= ) '"') xs
   | x == '#' = let (_, rest) = pickup (( /= ) '\n') xs in (Nothing, rest)
   | x == '\'' = g toChar $ pickup (( /= ) '\'') xs
   | isSpace x = (Nothing, xs)
   | otherwise = (Just $ Error "wrong", xs)
   where f gen (token, rest) = (Just $ gen $ x:token, rest)
         g gen (token, x:xs) = (Just $ gen token, xs)
         isIdentEx:isOperator:isBracket:_ = map (flip elem) ["_'" , "+-*/<>|?=@^$", "(){}[]"]
         isIdent x = isLetter x || x == '_'
         toChar [] = Error "too short"
         toChar [x] = LiteralOne x
         toChar (x:xs) = Error "too long"

tokenize [] = []
tokenize xs = case token of 
            Nothing -> tokens 
            Just t -> t:tokens
    where   (token, rest) = getToken xs
            tokens = tokenize rest

pickupTest line = token ++ ":" ++ rest where (token, rest) = pickup isDigit line
getTokenTest line = show token ++ ":" ++ rest where (token, rest) = getToken line
tokenizeTest line = intercalate "," $ map show $ tokenize line

tester test = forever $ do
    line <- getLine
    putStrLn $ test line

someFunc = tester tokenizeTest