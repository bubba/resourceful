{-# LANGUAGE TypeInType, TypeOperators #-}
{-# LANGUAGE TypeFamilies, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}

module SubIO where

import GHC.TypeLits
import Control.Concurrent
import Data.Type.Bool
import Data.Type.Set
import HeapMonad

newtype SubIO (a :: [j]) b = SubIO (IO b)
  deriving (Functor, Applicative, Monad)


instance HeapMonad SubIO j where
  (SubIO x) >>>= f = SubIO (x >>= \z -> let (SubIO y) = f z in y)
  (SubIO x) ||| (SubIO y) = SubIO (forkIO (x >> pure ()) >> y)


-- https://stackoverflow.com/questions/28666431/convert-type-level-list-to-a-value
class SymbolVals a where
  symbolVals :: proxy a -> [String]
instance SymbolVals '[] where
  symbolVals _ = []
instance (KnownSymbol x, SymbolVals xs) => SymbolVals (x ': xs) where
  symbolVals _ = symbolVal (Proxy :: Proxy x) : symbolVals (Proxy :: Proxy xs)

-- needed to force typechecker evaluation of the heap
runSubIO :: forall a heap. SymbolVals heap => SubIO heap a -> IO a
runSubIO (SubIO x) =
  let p = Proxy :: Proxy heap
      syms = symbolVals p
    in syms `seq` x

-- foo = (f >> f) >>>= \_ -> g
-- bar = foo >> subLift f

-- foo :: ("foo" ** "bar") String
-- foo = f >>= \x -> g

-- -- eventually there will be functions like
-- -- writeFile :: (fp :: FilePath) -> String -> SubIO fp ()

-- data NotSeparable
-- type family a ** b :: * where
--   (SubIO a b) ** (SubIO a d) = NotSeparable
--   (SubIO a b) ** (SubIO c d) = (SubIO a b, SubIO c d)

-- -- typechecks
-- bar :: (SubIO 42 Int) ** (SubIO "foo" String)
-- bar = (SubIO (return 0), SubIO (return "hey"))

-- -- doesn't typecheck
-- -- foo :: SubIO 32 Int ** SubIO 32 String
-- -- foo = (SubIO (return 0), SubIO (return "hey"))

-- -- now trying to get these to interleave monadically somehow

-- data Sep (a :: k) (b :: j) c where
--   RunA :: (SubIO a c) -> Sep a b c
--   RunB :: (SubIO b c) -> Sep a b c

-- instance Functor (Sep a b) where
--   fmap f (RunA x) = RunA (fmap f x)
--   fmap f (RunB x) = RunB (fmap f x)

-- instance Applicative (Sep a b) where
--   pure x = RunA (pure x)

-- runSep :: Sep a b c -> IO c
-- runSep (RunA (SubIO x)) = x
-- runSep (RunB (SubIO x)) = x

-- instance Monad (Sep a b) where
--   (RunA (SubIO x)) >>= f = RunA (SubIO (x >>= runSep . f))
--   (RunB (SubIO x)) >>= f = RunB (SubIO (x >>= runSep . f))

-- baz :: Sep "foo" "bar" Int
-- baz = do
--   x <- RunA (SubIO (return 42) :: SubIO "foo" Int)
--   y <- RunB (SubIO (return 12) :: SubIO "bar" Int)
--   return (x + y)

-- -- still allowed!
-- badbaz :: Sep "foo" "foo" Int
-- badbaz = do
--   x <- RunA (SubIO (return 42))
--   y <- RunB (SubIO (return 12))
--   return (x + y)


-- data family TestIO (heap :: h) a :: *
