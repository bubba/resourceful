-- Set : Type

data SubIO : (Eq j) => (heap : List j) -> Type -> Type where
     Sub : IO a -> SubIO j a

writeFile : (s : String) -> String -> SubIO [s] (Either FileError ())
writeFile fp s = Sub $ Prelude.File.writeFile fp s

consume : Eq a => List a -> List a -> List a
consume a b = if a `hasAny` b
            then []
            else union a b

foo : SubIO ([2] `consume` [3]) Int
foo = Sub (pure 2)

conc : SubIO i a -> SubIO j b -> SubIO (i `consume` j) (a, b)
conc (Sub x) (Sub y) = Sub (x >>= \a => y >>= \b => (a, b))

-- data Sep : k -> j -> Type -> Type where
--      SepA : SubIO k c -> Sep k j c
--      SepB : SubIO j c -> Sep k j c

-- implementation Functor (Sep a b) where
--   map f (SepA (Sub x)) = SepA (Sub (map f x))
--   map f (SepB (Sub x)) = SepB (Sub (map f x))

-- runSep : Sep k j a -> IO a
-- runSep (SepA (Sub x)) = x
-- runSep (SepB (Sub x)) = x

-- implementation Applicative (Sep a b) where
--   pure x = (SepA (Sub (pure x)))
--   sf <*> (SepA (Sub x)) = SepA (Sub (runSep sf <*> x))
--   sf <*> (SepB (Sub x)) = SepB (Sub (runSep sf <*> x))

-- implementation Monad (Sep a b) where
--   (SepA (Sub x)) >>= f = SepA (Sub (x >>= runSep . f))
--   (SepB (Sub x)) >>= f = SepB (Sub (x >>= runSep . f))

-- foo : Sep "foo.txt" "bar.txt" ()
-- foo = do
--   x <- SepA $ writeFile "foo.txt" "hey"
--   y <- SepB $ writeFile "bar.txt" "hey"
--   pure ()

-- bar : ("foo.txt" * "bar.txt" * "blah.txt") ()
-- bar = do
--   writeFile "foo.txt" : IO ()
--   writeFile "bar.txt" : IO ()

{-

Types t ::= Int | t -> t | t *_t t | IO x t
Terms e ::= x | e_1 e_2 | 

G |- e_1 : IO x t    G |- e_2 : IO y t
--------------------------------------
G |- e_1 >>= e_2 : x *_t y

G |- e : x *_t y
----------------
G |- e : y *_t x
-}
