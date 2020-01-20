handleRequest :: Connection -> IO ()
handleRequest conn = do
  a <- readFile "foo.txt"
  b <- receiveData conn
  sendData conn (a <> b)



writeFile :: IO ()
readFile :: IO String
concurrently :: IO a -> IO b -> IO (a, b)
x = writeFile "foo.txt" `concurrently` readFile "foo.txt"
