{-# LANGUAGE KindSignatures #-}

newtype IOSep k a = IOSep a

instance IO' (IOSep k)

instance IO' a => Monad a

data File

openFile :: IOSep File String
openFile = return "blah"

main' :: IO' a => a ()
main' = do
  foo <- openFile' "foo"
  bar <- readSocket' "/tmp/bar.sock"
  return ()


{-

and separately:

join :: IO a b * IO c d -> (b -> d -> IO e f) -> IO e f

join (readFile @foo) (readSocket @bar) <> :: IO e String

readFile :: IO (a :: File) String
writeFile :: String -> IO (a :: File) ()

readSocket :: IO (a :: Socket) String
writeSocket :: String -> IO (a :: Socket) ()

-}

{-

-- FileWorld is just a handle here

let f1 = openFile "foo.txt" w :: FileWorld* foo
    b1 = openFile "bar.txt" w :: FileWorld* bar
    f2 = writeFile f "hello" :: FileWorld* foo
    f3 = readFile f :: FileWOrld* foo, 
   
-}

class Monad a where
  (>>=) :: m a -> (a -> m b) -> m b
  return :: m a

newtype SubIO a b = SubIO (IO b)

instance Monad where

main :: SubIO foo * SubIO bar
main = do
  foo <- readFile "foo.txt" :: SubIO foo ()
  writeSocket "/tmp/blah.sock" :: SubIO ?? ()
  writeFile "bar.txt" foo

main = readFile >>= \foo ->
       writeSocket "/tmp/blah.sock" >>= \_ ->
       writeFile "bar.txt" foo
