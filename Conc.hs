{-# LANGUAGE DataKinds #-}

data Handle

main = do
  h <- openHandle "foo.txt" :: IO Handle
  writeHandle h "one" :: SubIO h ()
  s <- readHandle h :: SubIO h String
  writeHandle h "two" :: SubIO h ()
  writeHandle h "three" :: SubIO h ()

  j <- openHandle "bar.txt" :: IO Handle
  writeHandle j "one" :: SubIO j ()

e1 :: IO "x" ()
e2 :: IO "y" ()
conc :: IO "x" * "y" ()
conc = e1 || e2
e3 :: IO "z" ()
conc2 = IO "x" * "y" * "z" ()
notallowed = conc2 || e1

openHandle :: FilePath -> IO Handle
writeFile :: (h : Handle) -> String -> SubIO h ()
readFile :: (h : Handle) -> SubIO h String
(>>=) :: SubIO x a -> (a -> SubIO x b) -> SubIO x b
(||) :: SubIO x a -> SubIO y b -> SubIO (x * y) (a, b)
runSub :: SubIO x a -> IO a

foo = do
  h <- openHandle "bar.txt"
  i <- openHandle "foo.txt"
  (a,b) <- runSub $ (writeFile h "one" >>= \_ -> writeFile h "two") || readFile i
  return b

getLine :: IO String
getLine =  getChar >>= \c -> if c == '\n' then return "" else do l <- getLine; return (c:l)


-- bonus: is it possible to be polymorphic on read here, to also accept readwrite?
readHandle :: (h : Handle (Read | ReadWrite)) -> SubIO h String

cat = do
  ha <- openHandle "a" ReadMode
  hb <- openHandle "b" ReadMode
  (a, b) <- runSub (readHandle ha || readHandle hb)
  hc <- openHandle "c" WriteMode
  writeHandle hc (a <> b)

{-
 - frame rule:
 - {pre}code{post}
 - ----------------------
 - {pre*frame}code{post*frame}
 -
 - concurrency rule:
 - {pre1}proc1{post1} {pre2}proc2{proc2}
 - -------------------------------------
 - {pre1*pre2}proc1||proc2{post1*post2}
 -
 - frame rule:
 - e : IO_{x*y}
 - ------------------
 - e : IO_{x}
 -
 - concurrency rule:
 - e1 : IO_{x} e2 : IO_{y}
 - --------------------
 - e1 || e2 : IO_{x*y}
 -
 -}
