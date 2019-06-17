import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import System.IO.Unsafe (unsafePerformIO)

globalIntRef :: IORef Int
globalIntRef = unsafePerformIO $ newIORef 0

main :: IO ()
main = do
  x <- readIORef globalIntRef
  putStrLn $ show x
  succGlobal
  y <- readIORef globalIntRef
  putStrLn $ show y

succGlobal :: IO ()
succGlobal = do
  modifyIORef globalIntRef (+ 1)