module Main where
import qualified Data.Aeson as Aeson
import AWSLambda
import Test

main :: IO ()
main = testFunc

-- main = lambdaMain handler

handler :: Aeson.Value -> IO [Int]
handler evt = do
    testFunc
    print evt
    pure [1, 2, 3]
