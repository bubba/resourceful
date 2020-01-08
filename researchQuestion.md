# Research question

Separation logic allows specifications about a programs behaviour to
be defined in a way that scales well, by separating out concerns of
logic into "heaplets". It is built upon Hoare logic, which
inheritently lends itself to formally verifying the semantics of
imperative programming languages.  Furthermore, the typical
motiviational example given for separation logic usually revolves
around pointers and manual memory management.

We would like to investigate:
a) Using an intuitionistic type system to describe the properties that separation
logic guarantees. (See Birkedal, Torp-Smith, Yang)
b) Using the frame rule and concurrency rule of SL to "loosen" the
sequential nature of IO operations that functional languages typically
have in monadic and uniqueness typing based IO models.
c) Expanding the use of heaplets to apply to other real-world uses
such as separating out different concerns of IO operations, such as
networking, filesystem operations etc.


## Bonus idea
In-place update algorithms are efficient: these are notoriously
complicated to implement in pure functional languages. Can separation
logic be used to infer where in-place updates are possible while still
writing a program in a stateless, pure style?

Furthermore, linear typing and uniqueness typing keep track of how
many resources are used. Separation logic keeps track of where
resources are used. Is it possible to keep track of how many and where
resources are used, and if so, does this yield any practical benefit?


Encoding hoare triple into haskell type?
What does the hoare triple mean for howard-curry correspondance?


# Takeaways from separation logic

Separation conjuction: "and separately"
A * B

difference between AND
A * A /= A
A ∧ A = A


# semiring

+	: R x R -> R
.	: R x R -> R
1, 0 member of R
(R, ., 1) is a monoid
(R, +, 0) is a monoid

Can be used to track usage in linear types
Zero-one-many
R = {0, 1, ω}
⍴ + ω = ω
ω . ω = ω


Type-level separation logic for safe IO

Typical uses of separation logic are for pointer operations.
Can we use it for non pointer based operations?
I.e. the heap reperesents more than just memory.
How do they rejoin?

- Unordered IO

Network sockets
  dependent types to create them?
  
File descriptors/networks sockets writes can be reordererd

```haskell
writeSocket :: (sock : Socket) -> SockIO sock
writeFd :: (fd :: FileDescriptor) -> FileIO fd
(||) :: (a != b != c) FileIO a -> FileIO b -> FileIO c
-- equivalent to a -> fd * b -> fd * c -> fd
-- in separation logic
foo = do
  sock <- newSocket
  writeSocket sock
  writeFd stderr "hey" >>= writeFd stderr "hello"
```

Uniqueness types
```haskell
newSock :: String -> Sock
split :: IO () -> (a : Sock) -> *SockWorld a
write :: String -> *SockWorld a -> *SockWorld a
```

Monadic
```haskell
instance Monad (SockIO a) where
	...
newSock :: String -> Sock
split :: IO a -> (s : Sock) -> SockIO s ()
write :: String -> SockIO a ()
```


Filesystem

```haskell
openFile :: String -> IO File
writeFile :: String -> File -> IO ()
readFile :: File -> IO String

main = do
	foo <- openFile "foo"
	bar <- openFile "bar"
	writeFile "asdf" foo
	writeFile "hey" bar
	s <- readFile foo
	writeFile s bar
```

Filesystem uniqueness typing

```haskell
openFile : (a : FilePath) -> *FileIO a
writeFile : String -> *FileIO a -> *FileIO a
readFile : FileIO a -> String

main =
	let foo0 = openFile "foo" :: *FileIO foo
		bar0 = openFile "bar" :: *FileIO bar
		foo1 = writeFile "asdf" foo0 :: *FileIO foo
		bar1 = writeFile "hey" bar0 :: *FileIO bar
		s = readFile foo1 :: String
		bar2 = writeFile s bar1 :: FileIO bar
```

What's the benefit of separating FileIO out here?

Filesystem monadic CPS

```haskell
openFile : (a : FilePath) -> FileIO a () -> IO ()
writeFile : String -> FileIO a ()
readFile : FileIO a String

main = do
	s <- openFile "foo" $ writeFile "asdf" >> readFile
	openFile "bar" $ writeFile "hey" >> writeFile s
```

but then foo needs to be operated one before bar


breaking free of monadic sequencing
# TODO:
motivating example
example of oversequenced
example of not oversequenced

can we embed it within haskells system
if not then extend the type system or make one
