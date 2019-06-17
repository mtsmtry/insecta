module Kernel.Analyzer where
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Arrow
import Control.Applicative
import Utility
import Kernel.Parser
import Kernel.Rewriter
import Kernel.Data
import Kernel.Visualizer
