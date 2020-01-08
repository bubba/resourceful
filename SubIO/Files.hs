{-# LANGUAGE TypeApplications, TypeInType, RankNTypes, ScopedTypeVariables #-}
module SubIO.Files where

import Prelude hiding (readFile, writeFile, appendFile)
import qualified Prelude
import Data.Proxy
import GHC.TypeLits
import SubIO

someIO = do
  writeFile @"foo.txt" "hello"
  s <- readFile
  return s

someMoreIO x = do
  appendFile @"bar.txt" x
  readFile >>= SubIO . putStrLn

concExample = runSubIO $ someIO ||| someMoreIO "blah"

-- this type errors!
-- badConcExample = someIO ||| someMoreIO ||| someIO
-- this doesn't type error without the evaluation hack
-- badConcExample = runSubIO $ someIO ||| someMoreIO


readFile :: forall filePath. KnownSymbol filePath => SubIO '[filePath] String
readFile = fileOp Prelude.readFile

appendFile :: forall filePath. KnownSymbol filePath => String -> SubIO '[filePath] ()
appendFile x = fileOp (`Prelude.appendFile` x)

writeFile :: forall filePath. KnownSymbol filePath => String -> SubIO '[filePath] ()
writeFile x = fileOp (`Prelude.writeFile` x)

fileOp :: forall filePath a. KnownSymbol filePath => (FilePath -> IO a) -> SubIO '[filePath] a
fileOp f = let fp = symbolVal (Proxy :: Proxy filePath)
             in SubIO (f fp)
