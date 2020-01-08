{-# LANGUAGE TypeInType, KindSignatures, ScopedTypeVariables #-}
module PiType where

import Data.Proxy
import GHC.TypeLits

data Foo (x :: Symbol) a = Foo a

f :: forall x. KnownSymbol x => Foo x String
f = let p = Proxy :: Proxy x
        s = symbolVal p
        in Foo s
