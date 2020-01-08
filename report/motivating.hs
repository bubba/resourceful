handleRequest :: Connection -> IO ()
handleRequest conn = do
  a <- readFile "foo.txt"
  b <- receiveData conn
  sendData conn (a <> b)
