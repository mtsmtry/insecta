module Main where
import Test
import Control.Monad
import qualified Handler as H

main2 = H.main
main = testFunc
main3 = do
    forever $ do
        file <- readFile "test.txt"
        str <- getLine
        putStrLn $ H.mainFunc file str
    return ()