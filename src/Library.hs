module Library where
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

conjMaybe:: [Maybe a] -> Maybe [a]
conjMaybe [] = Just []
conjMaybe (x:xs) = (:) <$> x <*> conjMaybe xs

equalAsSet:: Eq a => [a] -> [a] -> Bool
equalAsSet xs ys = length xs == length ys && equalAsSet xs ys where
    equalAsSet:: Eq a => [a] -> [a] -> Bool
    equalAsSet [] [] = True
    equalAsSet (x:xs) ys = maybe False (equalAsSet xs) $ equalRest x ys []
    equalRest:: Eq a => a -> [a] -> [a] -> Maybe [a]
    equalRest x [] _ = Nothing
    equalRest x (y:ys) rest = if x == y then Just $ ys ++ rest else equalRest x ys (y:rest)

mapF:: (a -> m -> m) -> [a] -> m -> m
mapF f [] m = m
mapF f (x:xs) m = mapF f xs (f x m) 

toJsonWith:: Show k => Show v => (v -> String) -> M.Map k v -> String
toJsonWith f m = "{" ++ intercalate ", " (map (\(k, v)-> show k ++ ": " ++ f v) (M.toList m)) ++ "}"

toJsonFormatedWith:: Show k => Show v => (v -> String) -> M.Map k v -> String
toJsonFormatedWith f m = "{\t\n" ++ intercalate ",\n" (map (\(k, v)-> "\t" ++ show k ++ ": " ++ f v) (M.toList m)) ++ "\n}"

classify:: (a -> Bool) -> [a] -> ([a], [a])
classify f [] = ([], [])
classify f (x:xs) = if f x then (x:a, b) else (a, x:b) where (a, b) = classify f xs

maybeM:: Monad b => (a -> b ()) -> Maybe a -> b ()
maybeM = maybe (return ())

maybeN:: Monad b => (a -> b (Maybe c)) -> Maybe a -> b (Maybe c)
maybeN = maybe (return Nothing)