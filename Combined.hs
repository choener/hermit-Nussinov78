{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}
{-# OPTIONS_GHC -fllvm -optlo-O3 -optlc-O3 #-} -- this is fast...

module Main where

import Text.Printf
import System.Environment
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.ST
import Data.Char (toUpper, ord)
import Data.Primitive
--import Data.Vector.Fusion.Stream as S
--import Data.Vector.Fusion.Stream.Monadic as S
import Data.Vector.Fusion.Stream.Monadic as SM
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Prelude as P
import Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU
import Control.Monad.ST
import Data.Strict.Tuple
import GHC.Exts (inline)

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Zero as PA
-- import ADP.Fusion
-- import ADP.Fusion.Table
-- import ADP.Fusion.Apply
-- import ADP.Fusion.Empty
-- import ADP.Fusion.Classes
-- import ADP.Fusion.Chr
import Data.Array.Repa.Index.Subword
--import Data.PrimitiveArray.FillTables

import Debug.Trace
import Control.Arrow (second)
import System.IO.Unsafe

import HERMIT.Optimization.StreamFusion.ADPfusion

-- The signature

type Signature m a r =
  ( ()   -> a
  , Char -> a    -> a
  , a    -> Char -> a
  , Char -> a    -> Char -> a
  , a    -> a    -> a
  , SM.Stream m a -> m r
  )

-- the grammar

grammarFun
  ((empty,left,right,pair,split,h) :: Signature (ST s) Int Int)
  s
  (b :: GChr Char Char)
  (e :: Empty)
  =
  ( s, (
          empty <<< e         |||
          left  <<< b % s     |||
          right <<<     s % b |||
          pair  <<< b % s % b |||
          split <<<  s' % s'  ... h
--          split <<<  s % s  ... h
--            (apping split ( s , s)) ... h
--          zzzfun split (s', s') ... h
--          zzzfun split (s, s) ... h
      )
  )  where s' = toNonEmptyT s
{-# INLINE grammarFun #-}

-- pairmax algebra

aPairmax :: (Monad m) => Signature m Int Int
aPairmax = (empty,left,right,pair,split,h) where
  empty   _   = 0
  left    b s = s
  right s b   = s
  pair  l s r = if basepair l r then 1+s else -999999
  split  l r  = l+r
  {-# INLINE split #-}
  h = SM.foldl' max (-999999)
--  h = SM.foldl1' max
  {-# INLINE h #-}
{-# INLINE aPairmax #-}

basepair :: Char -> Char -> Bool
basepair l r = f l r where
  f 'C' 'G' = True
  f 'G' 'C' = True
  f 'A' 'U' = True
  f 'U' 'A' = True
  f 'G' 'U' = True
  f 'U' 'G' = True
  f _   _   = False
{-# INLINE basepair #-}

aPretty :: (Monad m) => Signature m String (SM.Stream m String)
aPretty = (empty,left,right,pair,split,h) where
  empty _     = ""
  left  b s   = "." P.++ s
  right   s b = s P.++ "."
  pair  l s r = "(" P.++ s P.++ ")"
  split l   r = l P.++ r
  h = return . id
{-# INLINE aPretty #-}

type CombSignature m e b =
  ( () -> (e, m (SM.Stream m b))
  , Char -> (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b))
  , (e, m (SM.Stream m b)) -> Char -> (e, m (SM.Stream m b))
  , Char -> (e, m (SM.Stream m b)) -> Char -> (e, m (SM.Stream m b))
  , (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b))
  , SM.Stream m (e, m (SM.Stream m b)) -> m (SM.Stream m b)
  )


-- * Boilerplate and driver, will be moved to library


nussinov78 inp = (arr ! (Z:.subword 0 n),bt) where
  (_,Z:.Subword (_:.n)) = bounds arr
  len  = P.length inp
  vinp = VU.fromList . P.map toUpper $ inp
  arr  = runST (forwardFun vinp)
  bt   = {- backtrack vinp arr -- -} [] :: [String] -- backtrack vinp arr
{-# NOINLINE nussinov78 #-}


--nussinov78Fill :: forall s . VU.Vector Char -> ST s (Z.U (Z:.Subword) Int)
forwardFun :: VU.Vector Char -> ST s (PA.Unboxed (Z:.Subword) Int)
forwardFun inp = do
  let n = VU.length inp
  !t' <- newWithM (Z:.subword 0 0) (Z:.subword 0 n) 0 -- fromAssocsM (Z:.subword 0 0) (Z:.subword 0 n) 0 []
  let t = mTblSw EmptyT t'
      {-# INLINE t #-}
  let b = chr inp
      {-# INLINE b #-}
  let e = Empty
      {-# INLINE e #-}
  fillFun $ grammarFun aPairmax t b e
--  upperTriS (Z:.gNussinov aPairmax t b e)
  freeze t'
{-# NOINLINE forwardFun #-}

--fillTable :: PrimMonad m => (MTbl Subword (PA.MutArr m (PA.Unboxed (Z:.Subword) Int)), (Subword -> m Int)) -> m ()
fillFun :: (MTbl Subword (PA.MutArr (ST s) (PA.Unboxed (Z:.Subword) Int)), (Subword -> ST s Int)) -> ST s ()
fillFun (MTbl _ tbl, f) = do
  let (_,Z:.Subword (0:.n)) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- (f $ subword i j)
    v `seq` writeM tbl (Z:.subword i j) v
{-# INLINE fillFun #-}




main = do
  as <- getArgs
  print as
  case as of
    ["gaplike"] -> do xs <- fmap lines getContents
                      P.mapM_ (doGAPlike 0) xs
    ["gaplike",k] -> do xs <- fmap lines getContents
                        P.mapM_ (doGAPlike (read k)) xs

doGAPlike :: Int -> String -> IO ()
doGAPlike k inp = do
  let (n,bt) = nussinov78 inp
  n `seq` printf "%s %d\n" inp n
  P.mapM_ putStrLn $ P.take k bt
{-# NOINLINE doGAPlike #-}





infixl 8 <<<
-- (<<<) f xs = \ij -> {- outerCheck (checkValidIndex (build xs) ij) . -} SM.map (apply (inline f) . getArg) . mkStream (build xs) (outer ij) $ ij
(<<<) f xs ij = SM.map (apply f . getArg) . mkStream (build xs) (outer ij) $ ij
{-# INLINE (<<<) #-}

apping f (x,y) = SM.map (apply (inline f) . getArg) . mkStream (Z:!:x:!:y) Outer
{-# INLINE apping #-}

infixl 5 ...
(...) s h = h . s
{-# INLINE (...) #-}

infixl 9 %
(%) = (:!:)
{-# INLINE (%) #-}

class Index i where
  type InOut  i :: *
  type ENZ    i :: *
  type PartialIndex i :: *
  type ParserRange i :: *
  outer :: i -> InOut i
  leftPartialIndex  :: i -> PartialIndex i
  rightPartialIndex :: i -> PartialIndex i
  fromPartialIndices :: PartialIndex i -> PartialIndex i -> i

class Build x where
  type Stack x :: *
  type Stack x = Z :!: x
  build :: x -> Stack x
  default build :: (Stack x ~ (Z :!: x)) => x -> Stack x
  build x = Z :!: x
  {-# INLINE build #-}

class (Monad m) => MkStream m x i where
  mkStream :: x -> InOut i -> i -> SM.Stream m (Elm x i)

class Elms x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

class Apply x where
  type Fun x :: *
  apply :: Fun x -> x

instance Apply (Z:.a -> res) where
  type Fun (Z:.a -> res) = a -> res
  apply fun (Z:.a) = fun a
  {-# INLINE apply #-}

instance Apply (Z:.a:.b -> res) where
  type Fun (Z:.a:.b -> res) = a->b -> res
  apply fun (Z:.a:.b) = fun a b
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c -> res) where
  type Fun (Z:.a:.b:.c -> res) = a->b->c -> res
  apply fun (Z:.a:.b:.c) = fun a b c
  {-# INLINE apply #-}

--checkValidIndex x i = validIndex x (getParserRange x i) i
--{-# INLINE checkValidIndex #-}

--class (Index i) => ValidIndex x i where
--  validIndex :: x -> ParserRange i -> i -> Bool
--  getParserRange :: x -> i -> ParserRange i

-- | 'outerCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

--outerCheck :: Monad m => Bool -> SM.Stream m a -> SM.Stream m a
--outerCheck b (SM.Stream step sS n) = b `seq` SM.Stream snew (Left (b,sS)) Unknown where
--  {-# INLINE [1] snew #-}
--  snew (Left  (False,s)) = return $ SM.Done
--  snew (Left  (True ,s)) = return $ SM.Skip (Right s)
--  snew (Right s        ) = do r <- step s
--                              case r of
--                                SM.Yield x s' -> return $ SM.Yield x (Right s')
--                                SM.Skip    s' -> return $ SM.Skip    (Right s')
--                                SM.Done       -> return $ SM.Done
--{-# INLINE outerCheck #-}

infixl 7 |||
(|||) xs ys = \ij -> xs ij SM.++ ys ij
{-# INLINE (|||) #-}

class EmptyTable x where
  toEmptyT :: x -> x
  toNonEmptyT :: x -> x

instance (EmptyENZ (ENZ i)) => EmptyTable (MTbl i xs) where
  toEmptyT    (MTbl enz xs) = MTbl (toEmptyENZ    enz) xs
  toNonEmptyT (MTbl enz xs) = MTbl (toNonEmptyENZ enz) xs
  {-# INLINE toEmptyT #-}
  {-# INLINE toNonEmptyT #-}

class EmptyENZ enz where
  toEmptyENZ    :: enz -> enz
  toNonEmptyENZ :: enz -> enz

chr xs = GChr (VU.unsafeIndex) xs
{-# INLINE chr #-}

data GChr r x = GChr !(VU.Vector x -> Int -> r) !(VU.Vector x)

instance Build (GChr r x)

--instance
--  ( ValidIndex ls Subword
--  , VU.Unbox x
--  ) => ValidIndex (ls :!: GChr r x) Subword where
--    validIndex (ls :!: GChr _ xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
--      i>=a && j<=VU.length xs -c && i+b<=j && validIndex ls abc ij
--    {-# INLINE validIndex #-}
--    getParserRange (ls :!: GChr _ _) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b+1:!:max 0 (c-1))
--    {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: GChr r x) Subword where
    data Elm (ls :!: GChr r x) Subword = ElmGChr !(Elm ls Subword) !r !Subword
    type Arg (ls :!: GChr r x) = Arg ls :. r
    getArg !(ElmGChr ls x _) = getArg ls :. x
    getIdx !(ElmGChr _ _ idx) = idx
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: GChr r x) Subword where
  mkStream !(ls :!: GChr f xs) Outer !ij@(Subword (i:.j)) =
    let dta = f xs (j-1)
    in  dta `seq` SM.map (\s -> ElmGChr s dta (subword (j-1) j)) $ mkStream ls Outer (subword i $ j-1)
  mkStream !(ls :!: GChr f xs) (Inner cnc szd) !ij@(Subword (i:.j))
    = SM.map (\s -> let Subword (k:.l) = getIdx s
                   in  ElmGChr s (f xs l) (subword l $ l+1)
            )
    $ mkStream ls (Inner cnc szd) (subword i $ j-1)
  {-# INLINE mkStream #-}

data Empty = Empty

empty = Empty
{-# INLINE empty #-}

--instance
--  ( ValidIndex ls Subword
--  ) => ValidIndex (ls :!: Empty) Subword where
--    validIndex (ls:!:Empty) abc ij@(Subword (i:.j)) = i==j && validIndex ls abc ij
--    {-# INLINE validIndex #-}

instance Build Empty

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Empty) Subword where
  data Elm (ls :!: Empty) Subword = ElmEmpty !(Elm ls Subword) !() !Subword
  type Arg (ls :!: Empty) = Arg ls :. ()
  getArg !(ElmEmpty ls () _) = getArg ls :. ()
  getIdx !(ElmEmpty _ _ i)   = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Empty) Subword where
  mkStream !(ls:!:Empty) Outer !ij@(Subword (i:.j))
    = SM.map (\s -> ElmEmpty s () (subword i j))
    $ SM.filter (\_ -> i==j)
    $ mkStream ls Outer ij
  {-# INLINE mkStream #-}

data MTbl i xs = MTbl !(ENZ i) !xs -- (PA.MutArr m (arr i x))

mTblSw :: ENE -> PA.MutArr m (arr (Z:.Subword) x) -> MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))
mTblSw = MTbl
{-# INLINE mTblSw #-}

instance Build (MTbl i x)

--instance
--  ( ValidIndex ls Subword
--  , Monad m
--  , PA.MPrimArrayOps arr (Z:.Subword) x
--  ) => ValidIndex (ls:!:MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
--  validIndex (_  :!: MTbl ZeroT _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
--  validIndex (ls :!: MTbl ene tbl) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
--    let (_,Z:.Subword (0:.n)) = PA.boundsM tbl
--        minsize = max b (if ene==EmptyT then 0 else 1)
--    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
--  {-# INLINE validIndex #-}
--  getParserRange (ls :!: MTbl ene _) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
--  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  data Elm (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword = ElmMTblSw !(Elm ls Subword) !x !Subword -- ElmBtTbl !(Elm ls Subword) !x !(m (SM.Stream m b)) !Subword
  type Arg (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) = Arg ls :. x
  getArg !(ElmMTblSw ls x _) = getArg ls :. x
  getIdx !(ElmMTblSw _  _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , Elms ls Subword
  , MkStream m ls Subword
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => MkStream m (ls :!: MTbl Subword (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  mkStream !(ls:!:MTbl ene tbl) Outer !ij@(Subword (i:.j))
    = SM.mapM (\s -> let (Subword (_:.l)) = getIdx s in PA.readM tbl (Z:.subword l j) >>= \z -> return $ ElmMTblSw s z (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NonEmptyT -> j-1 })
-- #ifdef HERMIT_CONCATMAP
--
  mkStream !(ls:!:MTbl ene tbl) (Inner _ szd) !ij@(Subword (i:.j))
    = SM.concatMap stepEnum
    $ mkStream ls (Inner NoCheck Nothing) ij where
      {-# INLINE stepRead #-}
      stepRead (s,l) = let (Subword (_:.k)) = getIdx s
                       in  PA.readM tbl (Z:.subword k l) >>= \z -> return $ ElmMTblSw s z (subword k l)
      -- perform one step in inner stream
      {-
      step s = let (Subword (_:.k)) = getIdx s
               in return . SM.mapM (\l -> PA.readM tbl (Z:.subword k l) >>= \z -> return $ ElmMTblSw s z (subword k l))
                  $ stepEnum s -}
      -- return stream of required indices
      {-# INLINE stepEnum #-}
      stepEnum s = let (Subword (_:.l)) = getIdx s
                       le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1}
                       l' = le -- case szd of Nothing -> le
                               --          Just z  -> max le (j-z)
                   in SM.mapM stepRead . SM.map (\k -> (s,k)) $ SM.enumFromStepN l' 1 (j-l'+1)
-- #else
--
{-
  mkStream !(ls:!:MTbl ene tbl) (Inner _ szd) !ij@(Subword (i:.j)) = SM.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    {-# INLINE [0] mk #-}
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    {-# INLINE [0] step #-}
    step !(s :!: k :!: l)
      | l > j = return SM.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ SM.Yield (ElmMTblSw s z (subword k l)) (s :!: k :!: l+1)
-- #endif
-}
  {-# INLINE mkStream #-}

data CheckNoCheck
  = Check
  | NoCheck
  deriving (Eq,Show)

data InnerOuter
  = Inner !CheckNoCheck !(Maybe Int)
  | Outer
  deriving (Eq,Show)

data ENE
  = EmptyT
  | NonEmptyT
  | ZeroT
  deriving (Eq,Show)

instance Index Subword where
  type InOut Subword = InnerOuter
  type ENZ   Subword = ENE
  type PartialIndex Subword = Int
  type ParserRange Subword = (Int :!: Int :!: Int)
  outer _ = Outer
  leftPartialIndex (Subword (i:.j)) = i
  rightPartialIndex (Subword (i:.j)) = j
  fromPartialIndices i j = subword i j
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

instance EmptyENZ ENE where
  toEmptyENZ ene  | ene==NonEmptyT = EmptyT
                  | otherwise      = ene
  toNonEmptyENZ ene | ene==EmptyT  = NonEmptyT
                    | otherwise    = ene
  {-# INLINE toEmptyENZ #-}
  {-# INLINE toNonEmptyENZ #-}

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# INLINE build #-}

--instance ValidIndex Z Subword where
--  {-# INLINE validIndex #-}
--  {-# INLINE getParserRange #-}
--  validIndex _ _ _ = True
--  getParserRange _ _ = (0 :!: 0 :!: 0)


instance Apply (Z:.a:.b:.c:.d -> res) where
  type Fun (Z:.a:.b:.c:.d -> res) = a->b->c->d -> res
  apply fun (Z:.a:.b:.c:.d) = fun a b c d
  {-# INLINE apply #-}

instance
  (
  ) => Elms Z ix where
  data Elm Z ix = ElmZ !ix
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ix) = ix
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Monad m => MkStream m Z Z where
  mkStream _ _ _ = SM.singleton (ElmZ Z)
  {-# INLINE mkStream #-}

instance
  ( Monad m
  ) => MkStream m Z Subword where
  mkStream Z Outer !(Subword (i:.j)) = SM.unfoldr step i where
    {-# INLINE [0] step #-}
    step !k
      | k==j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner NoCheck Nothing)  !(Subword (i:.j)) = SM.singleton $ ElmZ $ subword i i
  mkStream Z (Inner NoCheck (Just z)) !(Subword (i:.j)) = SM.unfoldr step i where
    {-# INLINE [0] step #-}
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise      = P.Nothing
  mkStream Z (Inner Check Nothing)   !(Subword (i:.j)) = SM.unfoldr step i where
    {-# INLINE [0] step #-}
    step !k
      | k<=j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner Check (Just z)) !(Subword (i:.j)) = SM.unfoldr step i where
    {-# INLINE [0] step #-}
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise      = P.Nothing
  {-# INLINE mkStream #-}

{-
infixl 8 <@<
(<@<) = zzzfun
{-# NOINLINE (<@<) #-}
-}

--
--infixl 8 `zzzfun`
zzzfun :: (Int -> Int -> Int)
      -> ( MTbl Subword (PA.MutArr (ST s) (PA.Unboxed (Z:.Subword) Int))
         , MTbl Subword (PA.MutArr (ST s) (PA.Unboxed (Z:.Subword) Int))
         )
      -> Subword
      -> SM.Stream (ST s) Int
-- (<@<) f !(!a,!b) !ij@(Subword((!i):.(!j)))
zzzfun f !(!a,!b) (Subword((!i):.(!j)))
  = SM.map (apply (inline f) . getArg')
  $ SM.mapM outerRead
  $ SM.concatMap stepEnum              -- can I assume that some form of eradication of concatmap/singleton happens? (no it doesn't, below in test everything works!)
  -- $ SM.singleton (ElmZ $ subword i i)
  $ SM.map (\k -> ElmZ $ subword k k)
  $ SM.enumFromStepN i 1 1
  where
--    Subword (i:.j) = ij
    MTbl _ !tbla = a
    MTbl _ !tblb = b
    getArg' (ElmMTblSw (ElmMTblSw (ElmZ _) z1 _) z2 _) = (Z:.z1:.z2)
    {-# INLINE  getArg' #-}
    outerRead !s = do let (Subword (_:.l)) = getIdx s
                      z <- PA.readM tbla (Z:.subword l j)
                      return $ ElmMTblSw s z (subword l j)
    {-# INLINE  outerRead #-}
    stepRead ((!s) :. (!l)) = let (Subword (_:.(!k))) = getIdx s
                              in  PA.readM tblb (Z:.subword k l) >>= \z -> return $ ElmMTblSw s z (subword k l)
    {-# INLINE  stepRead #-}
    -- concatMapM / return . SM.mapM doesn't work
    -- concatMap / SM.mapM works ?!
    stepEnum !s = let (Subword (_:.l)) = getIdx s
                      l' = l + 1
                  in SM.mapM stepRead . SM.map (\(!k) -> (s :. k)) $ SM.enumFromStepN l' 1 (j-l')
    {-# INLINE  stepEnum #-}
{-# INLINE zzzfun #-}
--

