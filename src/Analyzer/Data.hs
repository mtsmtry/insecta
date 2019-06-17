module Analyzer.Data(
    module Analyzer.Data,
    module Kernel.Data
) where
import Kernel.Data

-- Analyzer Monad
newtype Analyzer a = Analyzer { analyze::Context -> ([Message], Context, a) }

instance Functor Analyzer where
    fmap f (Analyzer g) = Analyzer $ \ctx -> let (msg, ctx', x) = g ctx in (msg, ctx', f x)

instance Applicative Analyzer where
    pure = return
    a <*> b = a >>= (<$> b)

instance Monad Analyzer where
    return x = Analyzer ([], , x)
    (Analyzer h) >>= f = Analyzer $ \ts ->
        let (msg, ctx, x) = h ts
            (Analyzer g) = f x
            (msg', ctx', x') = g ctx
        in  (msg ++ msg', ctx', x')

analyzeErrorM:: Ident -> String -> Analyzer (Maybe a)
analyzeErrorM ps str = Analyzer ([Message ps str], , Nothing)
analyzeErrorB:: Ident -> String -> Analyzer Bool
analyzeErrorB ps str = Analyzer ([Message ps str], , False)
analyzeError:: Ident -> String -> Analyzer ()
analyzeError ps str = Analyzer ([Message ps str], , ())

-- Context Accesser
updateContext selector f = Analyzer $ ([], , ()) . f
updateList f = Analyzer $ \ctx-> ([], ctx{conList=f $ conList ctx}, ())
updateSimp f = Analyzer $ \ctx-> ([], ctx{conSimp=f $ conSimp ctx}, ())
updateImpl f = Analyzer $ \ctx-> ([], ctx{conImpl=f $ conImpl ctx}, ())
updateEnt f = Analyzer $ \ctx-> ([], ctx{conEnt=f $ conEnt ctx}, ())

onContext:: (Context -> c) -> (c -> b -> a) -> b -> Analyzer a
onContext selector f trg = do
    omap <- fmap selector getContext
    return $ f omap trg

getContext:: Analyzer Context
getContext = Analyzer $ \ctx -> ([], ctx, ctx)

getLocalEntMap:: Analyzer EntityMap
getLocalEntMap = Analyzer $ \ctx -> ([], ctx, head $ conEnt ctx)

onOpeMap:: (OpeMap -> b -> a) -> b -> Analyzer a
onOpeMap = onContext conOpe


updateFunAttr:: String -> (FunAttr -> FunAttr) -> Analyzer ()
updateFunAttr name f = updateEnt $ map $ M.adjust (\ent-> ent{entFunAttr=f $ entFunAttr ent}) name

insertEntMap:: Ident -> Fom -> (Entity -> Entity) -> Analyzer ()
insertEntMap id ty f = updateEnt $ mapHead $ M.insert (idStr id) $ f $ makeEntity id ty

mapHead:: (a -> a) -> [a] -> [a]
mapHead f [] = []
mapHead f (x:xs) = f x:xs

insertEnt:: Ident -> Fom -> Analyzer ()
insertEnt name ty = insertEntMap name ty id

subScope:: Analyzer a -> Analyzer a
subScope subRountine = do
    updateEnt (M.empty:)
    res <- subRountine
    updateEnt tail
    return res

data DeclaArea = Local | Global
lookupEntWithArea:: String -> Analyzer (Maybe (Entity, DeclaArea))
lookupEntWithArea str = do
    (local:global) <- fmap conEnt getContext
    case M.lookup str local of
        Just ent -> return $ Just (ent, Local)
        Nothing -> case mapMaybe (M.lookup str) global of
            (x:xs) -> return $ Just (x, Global)
            _ -> return Nothing

lookupEnt:: String -> Analyzer (Maybe Entity)   
lookupEnt str = do
    res <- lookupEntWithArea str
    return $ fst <$> res

lookupPredRules:: String -> String -> Analyzer [Rule]
lookupPredRules pred trg = do
    rmap <- fmap conPred getContext
    return $ fromMaybe [] $ M.lookup pred rmap >>= M.lookup trg

-- Strategy
data StrategyOrigin =     StrategyOriginAuto 
                        | StrategyOriginWhole 
                        | StrategyOriginLeft 
                        | StrategyOriginFom Fom 
                        | StrategyOriginContext Fom 
                        | StrategyOriginWrong          

data StrategyRewrite =    CmdRewrite Command Fom 
                        | AssumeRewrite Command Fom Strategy 
                        | ForkRewrite [(Command, Strategy)] 
                        | InsertRewrite Fom 
                        | WrongRewrite

data StrategyOriginIdent = StrategyOriginIdent Ident StrategyOrigin 

data Strategy = Strategy StrategyOriginIdent [StrategyRewrite]