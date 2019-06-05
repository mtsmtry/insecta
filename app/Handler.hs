module Handler where
import AWSLambda
import AWSLambda.Events.APIGateway
import Control.Lens
import Codec.Binary.UTF8.String
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.ByteString as BS
import qualified Data.Aeson as A
import qualified Data.Text as T
import Data.Aeson.Embedded
import Data.Maybe
import qualified Data.CaseInsensitive as CI
import Data
import Library
import Analyzer
import Rewriter
import Parser
import Visualizer
import qualified Network.HTTP.Types.Header as HTTP

main:: IO ()
main = apiGatewayMain handler

toMapFromByteString:: [(BS.ByteString, Maybe BS.ByteString)] -> M.Map String String 
toMapFromByteString = M.fromList . mapMaybe toStringPair where
    toStringPair (k, Just v) = Just (decode $ BS.unpack k, decode $ BS.unpack v)
    toStringPair _ = Nothing

packMap:: [(String, String)] -> [(CI.CI BS.ByteString, BS.ByteString)]
packMap [] = []
packMap ((k, v):xs) = (CI.mk $ BS.pack $ encode k, BS.pack $ encode v):packMap xs

lookupHeader:: CI.CI BS.ByteString -> [(CI.CI BS.ByteString, BS.ByteString)] -> Maybe String
lookupHeader header map = listToMaybe (filter ((==header) . fst) map) >>= Just . decode . BS.unpack . snd

-- hOrigin
handler :: APIGatewayProxyRequest (Embedded A.Value) -> IO (APIGatewayProxyResponse String)
handler request = do
    file <- readFile "test.txt"
    let query = toMapFromByteString $ request ^. agprqQueryStringParameters
    let pathParams = request ^. agprqPathParameters
    let method = T.unpack <$> HM.lookup (T.pack "path") pathParams
    let result = case M.lookup "q" query of
            Just q -> mainFunc file q
            Nothing -> ""
    let headers = request ^. agprqHeaders
    let body = responseOK & responseBody ?~ result
    let body' = case lookupHeader HTTP.hOrigin headers of
            (Just origin) -> if origin `elem` ["https://localhost:5001", "https://www.incentknow.com"]
                then set agprsHeaders (packMap headers) body 
                else body
                where headers = [("Access-Control-Allow-Origin", origin), ("Access-Control-Allow-Credentials", "true")]
            Nothing -> body
    pure body'

mainFunc:: String -> String -> String
mainFunc prg str = res where
    (msgs, con) = buildProgram prg
    (msgs', _, res) = analyze (analyzeFunc str) con

analyzeFunc:: String -> Analyzer String
analyzeFunc str = do
    omap <- fmap conOpe getContext
    let exps = if null str then [] else parseExprs omap str
    foms <- subScope $ mapM (buildFomEx AllowUndefined) exps
    case foms of
        [Just fom] -> do
            rews <- simplify fom
            toJson rews
        [Just a, Just b] -> do
            mRes <- derivate (a, b)
            maybe (return "") toJson mRes
        _ -> return ""