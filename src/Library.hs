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

toJson m = toJsonWith show

toJsonWith:: Show k => Show v => (v -> String) -> M.Map k v -> String
toJsonWith f m = "{" ++ intercalate ", " (map (\(k, v)-> show k ++ ": " ++ f v) (M.toList m)) ++ "}"

toJsonFormatedWith:: Show k => Show v => (v -> String) -> M.Map k v -> String
toJsonFormatedWith f m = "{\t\n" ++ intercalate ",\n" (map (\(k, v)-> "\t" ++ show k ++ ": " ++ f v) (M.toList m)) ++ "\n}"

maybeFlip input nothing just = maybe nothing just input