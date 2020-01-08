-- $ ./Lazy 
-- hello world
-- this is the end
works = do
  x <- readFile "foo.txt"
  putStrLn x
  writeFile "foo.txt" "new stuff\n"

-- $ ./Lazy 
-- Lazy: foo.txt: openFile: resource busy (file is locked)
doesntWork = do
  x <- readFile "foo.txt"
  writeFile "foo.txt" "new stuff\n"
  putStrLn x
  
