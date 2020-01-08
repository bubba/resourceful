{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SubState where

import HeapMonad
import Data.Map (Map)
import Control.Monad.State

newtype SubState (x :: [j]) s a = SubState (State (Map j s) a)
  deriving (Functor, Applicative, Monad)

subGet :: key -> SubState '[key] s s
subGet key = SubState ((!! key) <$> get)

-- instance HeapMonad SubState heap where
--   (SubState s0 x0) >>>= f = SubState (x >>= \z -> let (SubState 
