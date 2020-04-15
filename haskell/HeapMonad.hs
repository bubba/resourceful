{-# LANGUAGE TypeInType, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies #-}
module HeapMonad where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Set

class Monad (m j) => HeapMonad (m :: [x] -> * -> *) j where
  (>>>=) :: m j a -> (a -> m k b) -> m (j ** k) b
  (|||) :: m j a -> m k b -> m (j ** k) b
  (|||) x f = x >>>= const f

type family Overlap a b :: Bool where
  Overlap '[] b = 'False
  Overlap (a ': as) b = If (MemberP a b) 'True (Overlap as b)

type family a ** b :: [c] where
  (a ** b) = If (Overlap a b)
                (TypeError ('Text "Heaps overlap!"))
                (a :++ b)

