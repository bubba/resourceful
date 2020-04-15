{-# LANGUAGE GADTs, PolyKinds, KindSignatures #-}
data family Sep (a :: k) (b :: j) c :: *

newtype instance Sep (IO c) a = SepA a b c
