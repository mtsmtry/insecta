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
import Data
import Library
import Analyzer
import Rewriter
import Parser
import Visualizer

main:: IO ()
main = apiGatewayMain handler

toMapFromByteString:: [(BS.ByteString, Maybe BS.ByteString)] -> M.Map String String 
toMapFromByteString = M.fromList . mapMaybe toStringPair where
    toStringPair (k, Just v) = Just (decode $ BS.unpack k, decode $ BS.unpack v)
    toStringPair _ = Nothing

toMapText:: [(T.Text, Maybe T.Text)] -> M.Map String String 
toMapText = M.fromList . mapMaybe toStringPair where
    toStringPair (k, Just v) = Just (T.unpack k, T.unpack v)
    toStringPair _ = Nothing

handler :: APIGatewayProxyRequest (Embedded A.Value) -> IO (APIGatewayProxyResponse String)
handler request = do
    file <- readFile "test.txt"
    let query = toMapFromByteString $ request ^. agprqQueryStringParameters
    let pathParams = request ^. agprqPathParameters
    let method = T.unpack <$> HM.lookup (T.pack "path") pathParams
    let result = case M.lookup "q" query of
            Just q -> mainFunc file q
            Nothing -> ""
    let headers = HM.fromList [(T.pack "", T.pack "")]
    let body = responseOK & responseBody ?~ result
    --let body' = set agprsHeaders headers body
    pure body

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