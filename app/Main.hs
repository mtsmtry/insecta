module Main where
import AWSLambda
import AWSLambda.Events.APIGateway
import Control.Lens
import Data.Aeson
import Data.Aeson.Embedded
import Test

main :: IO ()
-- main = testFunc

-- sls invoke local -f main = lambdaMain handler


-- main = lambdaMain handler

main = apiGatewayMain handler

handler :: APIGatewayProxyRequest (Embedded Value) -> IO (APIGatewayProxyResponse (Embedded [String]))
handler request = do
  putStrLn "This should go to logs"
  print $ request ^. requestBody
  pure $ responseOK & responseBodyEmbedded ?~ [show request]