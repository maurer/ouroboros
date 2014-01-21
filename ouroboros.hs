import Prelude hiding (init)
import System.Environment
import System.Exit
import Control.Monad.Error
import qualified Data.Map as Map
import Data.Map (Map)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import System.FilePath
import Crypto.Hash.SHA256
import Database.MongoDB
import Data.Text (pack)
import System.IO
import qualified Data.List as L
import System.Process

data OuroErr = TooFewArgs
             | UnknownErr
             | NoProgSpec CanonName
             | CacheMiss
             | MissingOrderedOut Int
             | MissingNamedOut String
             | StrErr String
               deriving Show
instance Error OuroErr where
  noMsg = UnknownErr
  strMsg = StrErr

type Ouro = Action (ErrorT OuroErr IO)

type Source = ArgVal SourceVal
type Sink = ArgVal SinkVal
data ArgVal a =
    Named String a
  | Order Int a deriving (Ord, Eq)
data SourceVal =
    StrVal String
  | InFileVal FilePath
  | Stdin deriving (Ord, Eq)
data SinkVal =
    Stdout
  | Stderr
  | OutFile FilePath deriving (Ord, Eq)
data ProgSpec = PS {
   inSpec  :: [String] -> [Source]
  ,outSpec :: [String] -> [Sink]
  }

dummySpec :: ProgSpec
dummySpec = PS {
     inSpec = zipWith (\n -> (Order n) . StrVal) [0..]
   , outSpec = \_ -> [Order 0 Stdout]
   }

getProgSpecs :: Ouro (Map CanonName ProgSpec)
getProgSpecs = return $ Map.singleton (CN "dummyProg") dummySpec

newtype CanonName = CN FilePath deriving (Show, Ord, Eq)

canonicalizeProg :: FilePath -> CanonName
canonicalizeProg = CN . takeFileName

type Hash = Binary

loadSourceVal :: SourceVal -> ByteString -> Ouro ByteString
loadSourceVal (StrVal s) _ = return $ BSC.pack s
loadSourceVal (InFileVal f) _ = liftIO $ BS.readFile f
loadSourceVal Stdin i = return $ i

loadArg :: ByteString -> Source -> Ouro ByteString
loadArg i (Named n v) = do 
  v' <- loadSourceVal v i
  return $ BS.concat ["named", BSC.pack n, v']
loadArg i (Order n v) = do
  v' <- loadSourceVal v i
  return $ BS.concat ["ordered", BSC.pack $ show n, v']

-- |From an invocation of a program, and a
--  specification of its argument behavior,
--  record an input hash to look up the output
--  in the cache.
recInputHash :: FilePath  -- ^Program name
             -> [String]  -- ^Program args
             -> ProgSpec  -- ^Arg parse spec
             -> ByteString
             -> Ouro Hash -- ^Database key
recInputHash prog args spec i = do
  progText <- liftIO $ BS.readFile prog
  argTexts <- mapM (loadArg i) $ L.sort $ inSpec spec args
  return $ Binary $ finalize $ updates init (progText : argTexts)
-- |Replay a program's output from cache data.
repOutput :: Hash
          -> [String]  -- ^Program args
          -> ProgSpec  -- ^Arg parse spec
          -> Ouro ()
repOutput h as spec = do
  mDoc <- findOne $ (select ["hash" =: h] "cache") {project = ["output" =: (1 :: Int)]}
  case mDoc of
    Just doc -> do
      let os = outSpec spec as
      acts <- mapM (fetchArgAction doc) os
      liftIO $ mapM_ outputArg acts
    Nothing -> throwError $ strMsg "CacheMiss"

fetchArgAction :: Document
               -> Sink
               -> Ouro (SinkVal, ByteString)
fetchArgAction doc (Named n t) = do
  v <- case doc !? (pack $ "output.named." ++ n) of
         Just (Binary v) -> return v
         Nothing -> throwError noMsg
  return (t, v)
fetchArgAction doc (Order n t) = do
  (Binary v) <- case doc !? ("output.ordered") of
                  Just v -> if length v > n
                    then return $ v !! n
                    else throwError noMsg
                  Nothing -> lift $ throwError $ MissingOrderedOut n
  return (t, v)
outputArg :: (SinkVal, ByteString)
          -> IO ()
outputArg (Stdout, b) = BS.hPutStr stdout b
outputArg (Stderr, b) = BS.hPutStr stderr b
outputArg (OutFile p, b) = BS.writeFile p b

-- |Run a program and record the output for
--  inclusion in the cache.
capOutput :: Hash
          -> FilePath     -- ^Program name
          -> [String]     -- ^Args
          -> ProgSpec     -- ^Arg parse spec
          -> ByteString
          -> Ouro ()
capOutput h p as spec is = do
  (i, o, e, pid) <- liftIO $ runInteractiveProcess p as Nothing Nothing
  (os, es, ec) <- liftIO $ do
    BS.hPutStr i is
    hClose i
    ec <- waitForProcess pid
    os <- BS.hGetContents o
    hClose o
    es <- BS.hGetContents e
    hClose e
    return (os, es, ec)
  vs <- mapM (loadOut os es) (outSpec spec as)
  let (ns,oo) = splitType vs
  let out = ["named"   =: map (\(f,v) -> (pack f) =: Binary v) ns
            ,"ordered" =: (map (Binary . snd) $ L.sort oo)
            ,"exitCode" =: (show ec)]
  n <- count (select ["hash" =: h] "cache")
  if n > 0
    then modify (select ["hash" =: h] "cache") ["$set" =: ["output" =: out]]
    else insert_ "cache" ["output" =: out
                         ,"hash"   =: h]
  liftIO $ BS.hPutStr stdout os
  liftIO $ BS.hPutStr stderr es
  where splitType :: [ArgVal ByteString]
                  -> ([(String, ByteString)],
                      [(Int, ByteString)])
        splitType = foldl (\(ss, os) av ->
          case av of
            Named n v -> ((n, v):ss, os)
            Order n v -> (ss, (n, v):os))
          ([], [])
        loadOut :: ByteString -> ByteString -> Sink -> Ouro (ArgVal ByteString)
        loadOut o e (Named n v) = fmap (Named n) $ loadOutArg o e v
        loadOut o e (Order n v) = fmap (Order n) $ loadOutArg o e v
        loadOutArg o _ Stdout = return o
        loadOutArg _ e Stderr = return e
        loadOutArg _ _ (OutFile f) = liftIO $ BS.readFile f

main :: IO ()
main = do
  r <- base
  case r of
    Left e -> do print e
                 exitFailure
    Right _ -> return ()

hasStdin :: ArgVal SourceVal -> Bool
hasStdin (Named _ Stdin) = True
hasStdin (Order _ Stdin) = True
hasStdin (Named _ _) = False
hasStdin (Order _ _) = False

base :: IO (Either OuroErr ())
base = runErrorT $ do
  cmdline   <- liftIO $ getArgs
  (p, args) <- case cmdline of
                 (p:args) -> return (p, args)
                 _ -> throwError TooFewArgs
  pipe <- liftIO $ runIOE $ connect (host "127.0.0.1")
  f <- access pipe master "ouroboros" $ do
    pss <- getProgSpecs
    let p' = canonicalizeProg p
    ps <- case Map.lookup p' pss of
            Just ps -> return ps
            Nothing -> lift $ throwError $ NoProgSpec p'
    i <- if [] == (filter hasStdin $ inSpec ps args)
           then return ""
           else liftIO $ BS.getContents
    inHash <- recInputHash p args ps i
    catchError (repOutput inHash args ps)
      (\_ -> capOutput inHash p args ps i)
  liftIO $ close pipe
  case f of
    Left e -> liftIO $ print e
    Right _ -> return ()
