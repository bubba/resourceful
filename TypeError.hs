{-# LANGUAGE DataKinds, RankNTypes, ScopedTypeVariables, TypeFamilies, PolyKinds, UndecidableInstances #-}
module TypeError where

import Data.Proxy
import GHC.TypeLits

newtype Foo (a :: k) b = Foo b

type family B :: String where
  B = TypeError ('Text "Yikes")

-- gives a type error
-- x :: Foo (TypeError ('Text "Woops")) ()
-- x = Foo ()

-- > :type y
-- y :: Foo (TypeError ...) ()

y :: Foo B ()
y = Foo ()

x :: forall (a :: k)  b. Proxy (Foo (a :: k) b) -> IO ()
x p = 
      symbolVal p `seq` pure ()
