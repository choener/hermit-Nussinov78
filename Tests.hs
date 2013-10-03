{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}
{-# OPTIONS_GHC -optlo-O3 -optlc-O3 #-} -- this is fast...

module Main where

import Data.Strict.Tuple
import Data.Vector as V
import Data.Vector.Fusion.Stream as S
--import Data.Vector.Fusion.Stream as VS
import Data.Vector.Fusion.Stream.Monadic as SM
import Data.Vector.Unboxed as U
import Data.Vector.Fusion.Stream.Size as S

import HERMIT.Optimization.StreamFusion.Vector



main :: IO ()
main = testDeep >>= print
--main = print $ testMainTest 10

{-
{-# NOINLINE testMainTest #-}
testMainTest :: Int -> Int
testMainTest k =
  --testDeep >>= print
  --testAAA >>= print
  (S.foldl' (+) 0
--    $   S.concatMap (S.enumFromStepN (1::Int) (1::Int))
    $   S.concatMap (S.enumFromStepN (1::Int) (1::Int))
    $   S.enumFromStepN (1::Int) (1::Int) k)
-}

class Deep x where
  deep :: x -> SM.Stream IO Int

instance Deep Int where
  deep !k = SM.enumFromStepN 1 1 k
  {-# INLINE deep #-}

instance Deep x => Deep (x :!: Int) where
  deep !(x :!: k) = SM.concatMap (SM.enumFromStepN 1 1) $ deep x
  {-# INLINE deep #-}

testDeep :: IO Int
testDeep = SM.foldl' (+) 0 $ deep (( (10::Int) :!: (12::Int)) :!: (14::Int))
{-# NOINLINE testDeep #-}

{-

{-# INLINE testInner1 #-}
testInner1 :: Stream IO Int -> Stream IO Int
testInner1 = SM.concatMap step where
  step !k = SM.enumFromStepN 1 1 k
  {-# INLINE step #-}

{-# INLINE testInner2 #-}   -- if we have something like this, both testInner1 and 2 need to be considered by hermit
testInner2 = testInner1

{-# NOINLINE testAAA #-}
testAAA :: IO Int
testAAA = SM.foldl' (+) 0 $ testInner1 $ testInner1 $ SM.singleton 10

{-# NOINLINE test1 #-}
test1 :: IO Int
test1 = SM.foldl' (+) 0 $ SM.concatMapM step $ SM.singleton 10 where
  step !k = return $ SM.enumFromStepN 1 1 k
  {-# INLINE step #-}
-}

