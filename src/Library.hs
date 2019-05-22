module Library where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as M
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative

conjMaybe:: [Maybe a] -> Maybe [a]
conjMaybe [] = Just []
conjMaybe (x:xs) = (:) <$> x <*> conjMaybe xs

toJson:: Show k => Show v => M.Map k v -> String
toJson m = "{" ++ concatMap (\(k, v)-> show k ++ ": " ++ show v) (M.toList m) ++ "}"

toJsonWith:: Show k => Show v => (v -> String) -> M.Map k v -> String
toJsonWith f m = "{\t\n" ++ concatMap (\(k, v)-> "\t" ++ show k ++ ": " ++ f v ++ "\n") (M.toList m) ++ "}"