{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Module    : Dependent.Walrus
-- Description : A small library of dependent types
-- Copyright   : (c) Dennis Gosnell, 2018
-- License     : BSD3
-- Stability   : experimental
-- Portability : POSIX
--
-- This is a small library of dependent types.  It provides indexed types like
-- 'Fin', 'Vec', and 'Matrix'.
--
-- This is mainly used in Termonad for "Termonad.Config.Colour" to represent
-- length-indexed colour lists.
--
-- This module implements a subset of the functionality from the abandoned
-- <http://hackage.haskell.org/package/type-combinators type-combinators> library.
-- Ideally this module would be split out to a separate package.
-- If you're interested in working on something like this, please see
-- <https://github.com/cdepillabout/termonad/issues/70 this issue> on Github.

module Dependent.Walrus (module X) where

import Data.Distributive (Distributive(distribute))
import Data.Foldable (foldl')
import qualified Data.Foldable as Data.Foldable
import Data.Functor.Rep (Representable(..), apRep, bindRep, distributeRep, pureRep)
import Data.Kind (Type)
import Data.MonoTraversable (Element, MonoFoldable, MonoFunctor, MonoPointed)
import Data.Singletons.Prelude
import Data.Singletons.TH
import Text.Show (showParen, showString)

import Dependent.Walrus.Fin as X
import Dependent.Walrus.HList as X
import Dependent.Walrus.IFin as X
import Dependent.Walrus.Peano as X
import Dependent.Walrus.Util as X

--------------------------
-- Misc VecT Operations --
--------------------------

-- TODO: These could be implemented?

-- data Range n l m = Range (IFin ('S n) l) (IFin ('S n) (l + m))
--   deriving (Show, Eq)

-- instance (Known (IFin ('S n)) l, Known (IFin ('S n)) (l + m))
--   => Known (Range n l) m where
--   type KnownC (Range n l) m
--     = (Known (IFin ('S n)) l, Known (IFin ('S n)) (l + m))
--   known = Range known known

-- updateRange :: Range n l m -> (Fin m -> f a -> f a) -> VecT n f a -> VecT n f a
-- updateRange = \case
--   Range  IFZ     IFZ    -> \_ -> id
--   Range (IFS l) (IFS m) -> \f -> onTail (updateRange (Range l m) f) \\ m
--   Range  IFZ    (IFS m) -> \f -> onTail (updateRange (Range IFZ m) $ f . FS)
--                                . onHead (f FZ) \\ m

-- setRange :: Range n l m -> VecT m f a -> VecT n f a -> VecT n f a
-- setRange r nv = updateRange r (\i _ -> index i nv)

-- updateSubmatrix
--   :: (ns ~ Fsts3 nlms, ms ~ Thds3 nlms)
--   => HList (Uncur3 Range) nlms -> (HList Fin ms -> a -> a) -> M ns a -> M ns a
-- updateSubmatrix = \case
--   Ø              -> \f -> (f Ø <$>)
--   Uncur3 r :< rs -> \f -> onMatrix . updateRange r $ \i ->
--     asM . updateSubmatrix rs $ f . (i :<)

-- setSubmatrix
--   :: (ns ~ Fsts3 nlms, ms ~ Thds3 nlms)
--   => HList (Uncur3 Range) nlms -> M ms a -> M ns a -> M ns a
-- setSubmatrix rs sm = updateSubmatrix rs $ \is _ -> indexMatrix is sm



---------
-- Vec --
---------

data Vec (n :: Peano) :: Type -> Type where
  EmptyVec :: Vec 'Z a
  (:*) :: !a -> !(Vec n a) -> Vec ('S n) a
  deriving anyclass MonoFoldable

infixr 6 :*

-- | Data constructor for ':*'.
pattern ConsVec :: (a :: Type) -> Vec n a -> Vec ('S n) a
pattern ConsVec a vec = a :* vec

deriving instance Eq a => Eq (Vec n a)
deriving instance Ord a => Ord (Vec n a)
deriving instance Show a => Show (Vec n a)

deriving instance Functor (Vec n)
deriving instance Foldable (Vec n)

instance MonoFunctor (Vec n a)

instance SingI n => MonoPointed (Vec n a)

instance SingI n => Applicative (Vec n) where
  pure a = replaceVec_ a

  (<*>) = apVec ($)

instance SingI n => Distributive (Vec n) where
  distribute :: Functor f => f (Vec n a) -> Vec n (f a)
  distribute = distributeRep

instance SingI n => Representable (Vec n) where
  type Rep (Vec n) = Fin n

  tabulate :: (Fin n -> a) -> Vec n a
  tabulate = genVec_

  index :: Vec n a -> Fin n -> a
  index = flip indexVec

instance SingI n => Monad (Vec n) where
  (>>=) :: Vec n a -> (a -> Vec n b) -> Vec n b
  (>>=) = bindRep

type instance Element (Vec n a) = a

genVec_ :: SingI n => (Fin n -> a) -> Vec n a
genVec_ = genVec sing

genVec :: SPeano n -> (Fin n -> a) -> Vec n a
genVec SZ _ = EmptyVec
genVec (SS n) f = f FZ :* genVec n (f . FS)

indexVec :: Fin n -> Vec n a -> a
indexVec FZ (a :* _) = a
indexVec (FS n) (_ :* vec) = indexVec n vec

singletonVec :: a -> Vec N1 a
singletonVec a = ConsVec a EmptyVec

replaceVec :: Sing n -> a -> Vec n a
replaceVec SZ _ = EmptyVec
replaceVec (SS n) a = a :* replaceVec n a

imapVec :: forall n a b. (Fin n -> a -> b) -> Vec n a -> Vec n b
imapVec _ EmptyVec = EmptyVec
imapVec f (a :* as) = f FZ a :* imapVec (\fin' vec -> f (FS fin') vec) as

replaceVec_ :: SingI n => a -> Vec n a
replaceVec_ = replaceVec sing

apVec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
apVec _ EmptyVec _ = EmptyVec
apVec f (a :* as) (b :* bs) = f a b :* apVec f as bs

onHeadVec :: (a -> a) -> Vec ('S n) a -> Vec ('S n) a
onHeadVec f (a :* as) = f a :* as

dropVec :: Sing m -> Vec (m + n) a -> Vec n a
dropVec SZ vec = vec
dropVec (SS n) (_ :* vec) = dropVec n vec

takeVec :: IFin n m -> Vec n a -> Vec m a
takeVec IFZ _ = EmptyVec
takeVec (IFS n) (a :* vec) = a :* takeVec n vec

updateAtVec :: Fin n -> (a -> a) -> Vec n a -> Vec n a
updateAtVec FZ f (a :* vec)  = f a :* vec
updateAtVec (FS n) f (a :* vec)  = a :* updateAtVec n f vec

setAtVec :: Fin n -> a -> Vec n a -> Vec n a
setAtVec fin' a = updateAtVec fin' (const a)

-- | Create a 'Vec' of length @n@ where every element is @a@.
--
-- >>> replicateVec (sing @N3) 'd'
-- 'd' :* ('d' :* ('d' :* EmptyVec))
replicateVec :: Sing n -> a -> Vec n a
replicateVec SZ _ = EmptyVec
replicateVec (SS n) a = ConsVec a $ replicateVec n a

-- | Just like 'replicateVec' but take the length argument implicitly.
--
-- >>> replicateVec_ @N2 "hello"
-- "hello" :* ("hello" :* EmptyVec)
replicateVec_ :: forall n a. SingI n => a -> Vec n a
replicateVec_ = replicateVec sing

-- | Convert a list to a 'Vec'.
--
-- Discards any leftover values from the list.
--
-- >>> fromListVec (sing @N3) [1,2,3,4,5]
-- Just (1 :* (2 :* (3 :* EmptyVec)))
--
-- If the list doesn't contain enough elements,
-- return 'Nothing':
--
-- >>> fromListVec (sing @N3) [1,2]
-- Nothing
fromListVec :: Sing n -> [a] -> Maybe (Vec n a)
fromListVec n = fmap fst . fromListLeftOverVec n

-- | Like 'fromListVec' but take the 'Vec' length
-- implicitly.
--
-- >>> fromListVec_ @N2 [1..]
-- Just (1 :* (2 :* EmptyVec))
fromListVec_ :: SingI n => [a] -> Maybe (Vec n a)
fromListVec_ = fromListVec sing

-- | Just like 'fromListVec', but return any leftover
-- items from the list.
--
-- >>> fromListLeftOverVec (sing @N3) [1,2,3,4,5]
-- Just (1 :* (2 :* (3 :* EmptyVec)),[4,5])
fromListLeftOverVec
  :: Sing n -> [a] -> Maybe (Vec n a, [a])
fromListLeftOverVec SZ leftOverAs = Just (EmptyVec, leftOverAs)
fromListLeftOverVec (SS _) [] = Nothing
fromListLeftOverVec (SS n) (a:as) = do
  (tailVec, leftOverAs) <- fromListLeftOverVec n as
  pure (ConsVec a tailVec, leftOverAs)

-- | Just like 'fromListLeftOverVec' but take the 'Vec'
-- length implicitly.
fromListLeftOverVec_
  :: SingI n => [a] -> Maybe (Vec n a, [a])
fromListLeftOverVec_ = fromListLeftOverVec sing

-- | Unsafe version of 'fromListVec'.
unsafeFromListVec :: Sing n -> [a] -> Vec n a
unsafeFromListVec n as =
  case fromListVec n as of
    Just vec -> vec
    Nothing ->
      error $
        "unsafeFromListVec: couldn't create a length " <>
        show n <> " vector from the input list"

unsafeFromListVec_ :: SingI n => [a] -> Vec n a
unsafeFromListVec_ = unsafeFromListVec sing

zipWithVec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithVec _ EmptyVec EmptyVec = EmptyVec
zipWithVec f (a :* as) (b :* bs) = f a b :* zipWithVec f as bs

------------
-- Matrix --
------------

-- | This is a type family that gives us arbitrarily-ranked matricies.
--
-- For example, this is a Matrix with three dimensions.  It is represented as a
-- 'Vec' containing a 'Vec' containing a 'Vec':
--
-- >>> Refl :: MatrixTF '[N3, N9, N7] Float :~: Vec N3 (Vec N9 (Vec N7 Float))
-- Refl
--
-- A Matrix with no dimensions represents a scalar value:
--
-- >>> Refl :: MatrixTF '[] Float :~: Float
-- Refl
type family MatrixTF (ns :: [Peano]) (a :: Type) :: Type where
  MatrixTF '[] a = a
  MatrixTF (n ': ns) a = Vec n (MatrixTF ns a)

newtype Matrix ns a = Matrix
  { unMatrix :: MatrixTF ns a
  }
  deriving anyclass (MonoFoldable)

type instance Element (Matrix ns a) = a

---------------------------------
-- Defunctionalization Symbols --
---------------------------------

type MatrixTFSym2 (ns :: [Peano]) (t :: Type) = (MatrixTF ns t :: Type)

data MatrixTFSym1 (ns :: [Peano]) (z :: TyFun Type Type)
  = forall (arg :: Type).  SameKind (Apply (MatrixTFSym1 ns) arg) (MatrixTFSym2 ns arg) => MatrixTFSym1KindInference

type instance Apply (MatrixTFSym1 l1) l2 = MatrixTF l1 l2

type role MatrixTFSym0 phantom

data MatrixTFSym0 (l :: TyFun [Peano] (Type ~> Type))
  = forall (arg :: [Peano]).  SameKind (Apply MatrixTFSym0 arg) (MatrixTFSym1 arg) => MatrixTFSym0KindInference

type instance Apply MatrixTFSym0 l = MatrixTFSym1 l

type role MatrixTFSym1 phantom phantom

----------------------
-- Matrix Functions --
----------------------

eqSingMatrix :: forall (peanos :: [Peano]) (a :: Type). Eq a => Sing peanos -> Matrix peanos a -> Matrix peanos a -> Bool
eqSingMatrix = compareSingMatrix (==) True (&&)

ordSingMatrix :: forall (peanos :: [Peano]) (a :: Type). Ord a => Sing peanos -> Matrix peanos a -> Matrix peanos a -> Ordering
ordSingMatrix = compareSingMatrix compare EQ f
  where
    f :: Ordering -> Ordering -> Ordering
    f EQ o = o
    f o _ = o

compareSingMatrix ::
     forall (peanos :: [Peano]) (a :: Type) (c :: Type)
   . (a -> a -> c)
  -> c
  -> (c -> c -> c)
  -> Sing peanos
  -> Matrix peanos a
  -> Matrix peanos a
  -> c
compareSingMatrix f _ _ SNil (Matrix a) (Matrix b) = f a b
compareSingMatrix _ empt _ (SCons SZ _) (Matrix EmptyVec) (Matrix EmptyVec) = empt
compareSingMatrix f empt combine (SCons (SS peanoSingle) moreN) (Matrix (a :* moreA)) (Matrix (b :* moreB)) =
  combine
    (compareSingMatrix f empt combine moreN (Matrix a) (Matrix b))
    (compareSingMatrix f empt combine (SCons peanoSingle moreN) (Matrix moreA) (Matrix moreB))

fmapSingMatrix :: forall (peanos :: [Peano]) (a :: Type) (b ::Type). Sing peanos -> (a -> b) -> Matrix peanos a -> Matrix peanos b
fmapSingMatrix SNil f (Matrix a) = Matrix $ f a
fmapSingMatrix (SCons SZ _) _ (Matrix EmptyVec) = Matrix EmptyVec
fmapSingMatrix (SCons (SS peanoSingle) moreN) f (Matrix (a :* moreA)) =
  let matA = fmapSingMatrix moreN f (Matrix a)
      matB = fmapSingMatrix (SCons peanoSingle moreN) f (Matrix moreA)
  in consMatrix matA matB

consMatrix :: Matrix ns a -> Matrix (n ': ns) a -> Matrix ('S n ': ns) a
consMatrix (Matrix a) (Matrix as) = Matrix $ ConsVec a as

toListMatrix ::
     forall (peanos :: [Peano]) (a :: Type).
     Sing peanos
  -> Matrix peanos a
  -> [a]
toListMatrix SNil (Matrix a) = [a]
toListMatrix (SCons SZ _) (Matrix EmptyVec) = []
toListMatrix (SCons (SS peanoSingle) moreN) (Matrix (a :* moreA)) =
  toListMatrix moreN (Matrix a) <> toListMatrix (SCons peanoSingle moreN) (Matrix moreA)

genMatrix ::
     forall (ns :: [Peano]) (a :: Type).
     Sing ns
  -> (HList Fin ns -> a)
  -> Matrix ns a
genMatrix SNil f = Matrix $ f EmptyHList
genMatrix (SCons (n :: SPeano foo) (ns' :: Sing oaoa)) f =
  Matrix $ (genVec n $ (gagaga :: Fin foo -> MatrixTF oaoa a) :: Vec foo (MatrixTF oaoa a))
  where
    gagaga :: Fin foo -> MatrixTF oaoa a
    gagaga faaa = unMatrix $ (genMatrix ns' $ byebye faaa :: Matrix oaoa a)

    byebye :: Fin foo -> HList Fin oaoa -> a
    byebye faaa = f . ConsHList faaa

genMatrix_ :: SingI ns => (HList Fin ns -> a) -> Matrix ns a
genMatrix_ = genMatrix sing

-- | Just like 'replicateVec' but for a 'Matrix'.
--
-- >>> replicateMatrix (sing @'[N2, N3]) 'b'
-- Matrix {unMatrix = ('b' :* ('b' :* ('b' :* EmptyVec))) :* (('b' :* ('b' :* ('b' :* EmptyVec))) :* EmptyVec)}
replicateMatrix :: Sing ns -> a -> Matrix ns a
replicateMatrix ns a = genMatrix ns (const a)

-- | Just like 'replicateMatrix', but take the length argument implicitly.
--
-- >>> replicateMatrix_ @'[N2,N2,N2] 0
-- Matrix {unMatrix = ((0 :* (0 :* EmptyVec)) :* ((0 :* (0 :* EmptyVec)) :* EmptyVec)) :* (((0 :* (0 :* EmptyVec)) :* ((0 :* (0 :* EmptyVec)) :* EmptyVec)) :* EmptyVec)}
replicateMatrix_ :: SingI ns => a -> Matrix ns a
replicateMatrix_ a = replicateMatrix sing a

indexMatrix :: HList Fin ns -> Matrix ns a -> a
indexMatrix EmptyHList (Matrix a) = a
indexMatrix (i :< is) (Matrix vec) = indexMatrix is $ Matrix (indexVec i vec)

imapMatrix :: forall (ns :: [Peano]) a b. Sing ns -> (HList Fin ns -> a -> b) -> Matrix ns a -> Matrix ns b
imapMatrix SNil f (Matrix a) = Matrix (f EmptyHList a)
imapMatrix (SCons _ ns) f matrix =
  onMatrixTF
    (imapVec (\fin' -> onMatrix (imapMatrix ns (\hlist -> f (ConsHList fin' hlist)))))
    matrix

imapMatrix_ :: SingI ns => (HList Fin ns -> a -> b) -> Matrix ns a -> Matrix ns b
imapMatrix_ = imapMatrix sing

onMatrixTF :: (MatrixTF ns a -> MatrixTF ms b) -> Matrix ns a -> Matrix ms b
onMatrixTF f (Matrix mat) = Matrix $ f mat

onMatrix :: (Matrix ns a -> Matrix ms b) -> MatrixTF ns a -> MatrixTF ms b
onMatrix f = unMatrix . f . Matrix

updateAtMatrix :: HList Fin ns -> (a -> a) -> Matrix ns a -> Matrix ns a
updateAtMatrix EmptyHList _ mat = mat
updateAtMatrix (n :< ns) f mat =
  onMatrixTF (updateAtVec n (onMatrix (updateAtMatrix ns f))) mat

setAtMatrix :: HList Fin ns -> a -> Matrix ns a -> Matrix ns a
setAtMatrix fins a = updateAtMatrix fins (const a)

-- | Multiply two matricies together.  This uses normal matrix multiplication,
-- not the Hadamard product.
--
-- When @m@ is 0, this produces a @n@ by @o@ matrix where all elements are 0.
--
-- >>> let mat1 = replicateMatrix_ @'[N3, N0] 3
-- >>> let mat2 = replicateMatrix_ @'[N0, N2] 3
-- >>> matrixMult (sing @N3) (sing @N0) (sing @N2) mat1 mat2
-- Matrix {unMatrix = (0 :* (0 :* EmptyVec)) :* ((0 :* (0 :* EmptyVec)) :* ((0 :* (0 :* EmptyVec)) :* EmptyVec))}
--
-- Otherwise, this does normal matrix multiplication:
--
-- >>> let Just mat1 = fromListMatrix (sing @'[N2, N3]) [1..6]
-- >>> mat1
-- Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* ((4 :* (5 :* (6 :* EmptyVec))) :* EmptyVec)}
-- >>> let Just mat2 = fromListMatrix (sing @'[N3, N2]) [7..12]
-- >>> mat2
-- Matrix {unMatrix = (7 :* (8 :* EmptyVec)) :* ((9 :* (10 :* EmptyVec)) :* ((11 :* (12 :* EmptyVec)) :* EmptyVec))}
-- >>> matrixMult (sing @N2) (sing @N3) (sing @N2) mat1 mat2
-- Matrix {unMatrix = (58 :* (64 :* EmptyVec)) :* ((139 :* (154 :* EmptyVec)) :* EmptyVec)}
matrixMult
  :: forall n m o a
   . Num a
  => Sing n
  -> Sing m
  -> Sing o
  -> Matrix '[n, m] a
  -> Matrix '[m, o] a
  -> Matrix '[n, o] a
matrixMult n SZ o _ _ = replicateMatrix (doubletonList n o) 0
matrixMult n m o mat1 mat2 = genMatrix (doubletonList n o) go
  where
    go :: HList Fin '[n, o] -> a
    go (finN :< finO :< EmptyHList) =
      let rowVec = getRowMatrix finN mat1
          colVec = getColMatrix finO mat2
      in sum $ zipWithVec (*) rowVec colVec

-- | Get the specified row of a 'Matrix'.
--
-- >>> let createVal finRow finCol = toIntFin finRow * 2 + toIntFin finCol
-- >>> let mat1 = genMatrix (sing @'[N3, N2]) (\(r :< c :< EmptyHList) -> createVal r c)
-- >>> mat1
-- Matrix {unMatrix = (0 :* (1 :* EmptyVec)) :* ((2 :* (3 :* EmptyVec)) :* ((4 :* (5 :* EmptyVec)) :* EmptyVec))}
--
-- Get the first row of a 'Matrix':
--
-- >>> getRowMatrix FZ mat1
-- 0 :* (1 :* EmptyVec)
--
-- Get the third row of a 'Matrix':
--
-- >>> getRowMatrix (FS (FS FZ)) mat1
-- 4 :* (5 :* EmptyVec)
getRowMatrix :: forall n m a. Fin n -> Matrix '[n, m] a -> Vec m a
getRowMatrix FZ (Matrix (v :* _)) = v
getRowMatrix (FS n) (Matrix (_ :* next)) = getRowMatrix n (Matrix next)

-- | Get the specified column of a 'Matrix'.
--
-- >>> let createVal finRow finCol = toIntFin finRow * 3 + toIntFin finCol
-- >>> let mat1 = genMatrix (sing @'[N2, N3]) (\(r :< c :< EmptyHList) -> createVal r c)
-- >>> mat1
-- Matrix {unMatrix = (0 :* (1 :* (2 :* EmptyVec))) :* ((3 :* (4 :* (5 :* EmptyVec))) :* EmptyVec)}
--
-- Get the first column of a 'Matrix':
--
-- >>> getColMatrix FZ mat1
-- 0 :* (3 :* EmptyVec)
--
-- Get the third column of a 'Matrix':
--
-- >>> getColMatrix (FS (FS FZ)) mat1
-- 2 :* (5 :* EmptyVec)
getColMatrix :: forall n m a. Fin m -> Matrix '[n, m] a -> Vec n a
getColMatrix fin (Matrix vs) = fmap (indexVec fin) vs

-- | Similar to 'fromListLeftOverVec' but for a 'Matrix'.
--
-- If there are not enough values in the list, then 'Nothing' is returned:
--
-- >>> fromListLeftOverMatrix (sing @'[N2, N3]) []
-- Nothing
--
-- A 'Matrix' without a rank just uses a single value from the list:
--
-- >>> fromListLeftOverMatrix (sing @'[]) [1,2,3]
-- Just (Matrix {unMatrix = 1},[2,3])
--
-- A 'Matrix' with a single rank just wraps a 'Vec':
--
-- >>> fromListLeftOverMatrix (sing @'[N3]) [1,2,3,4,5,6]
-- Just (Matrix {unMatrix = 1 :* (2 :* (3 :* EmptyVec))},[4,5,6])
--
-- A 'Matrix' with multiple ranks:
--
-- >>> fromListLeftOverMatrix (sing @'[N2, N3]) [1..8]
-- Just (Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* ((4 :* (5 :* (6 :* EmptyVec))) :* EmptyVec)},[7,8])
--
-- If one of the ranks has 0 elements, then the output matrix also has 0 elements:
--
-- >>> fromListLeftOverMatrix (sing @'[N0, N3]) [1..4]
-- Just (Matrix {unMatrix = EmptyVec},[1,2,3,4])
-- >>> fromListLeftOverMatrix (sing @'[N3, N0]) [1..4]
-- Just (Matrix {unMatrix = EmptyVec :* (EmptyVec :* (EmptyVec :* EmptyVec))},[1,2,3,4])
fromListLeftOverMatrix :: forall ns a. Sing ns -> [a] -> Maybe (Matrix ns a, [a])
fromListLeftOverMatrix SNil [] = Nothing
fromListLeftOverMatrix SNil (a : leftOverAs) = Just (Matrix a, leftOverAs)
fromListLeftOverMatrix (SCons n SNil) as =
  fmap (\(vec, leftOverAs) -> (Matrix vec, leftOverAs)) $ fromListLeftOverVec n as
fromListLeftOverMatrix (SCons (n :: Sing (nt :: Peano)) (ms :: Sing ms)) as = do
    (matrixList, leftOverAs) <- go
    (finalVecs :: Vec nt (Matrix ms a)) <- fromListVec n matrixList
    let (finalMatrix :: MatrixTF ns a) = fmap unMatrix finalVecs
    pure (Matrix finalMatrix, leftOverAs)
  where
    -- This outputs a list of submatricies.  This list should be @n@ elements
    -- long.
    go :: Maybe ([Matrix ms a], [a])
    go = foldl' f (Just ([], as)) [1 .. fromSing n]

    f :: Maybe ([Matrix ms a], [a]) -> x -> Maybe ([Matrix ms a], [a])
    f Nothing _ = Nothing
    f (Just (mats, remainingAs)) _ = do
      (newMat, leftOverAs) <- fromListLeftOverMatrix ms remainingAs
      pure (mats ++ [newMat], leftOverAs)

-- | Just like 'fromListLeftOverMatrix' but passes the 'Matrix' ranks implicitly.
fromListLeftOverMatrix_ :: forall ns a. SingI ns => [a] -> Maybe (Matrix ns a, [a])
fromListLeftOverMatrix_ = fromListLeftOverMatrix sing

-- | Just like 'fromListLeftOverMatrix' but don't return the leftover elements from
-- the input list.
fromListMatrix :: forall ns a. Sing ns -> [a] -> Maybe (Matrix ns a)
fromListMatrix ns = fmap fst . fromListLeftOverMatrix ns

-- | Just like 'fromListMatrix' but passes the 'Matrix' ranks implicitly.
fromListMatrix_ :: forall ns a. SingI ns => [a] -> Maybe (Matrix ns a)
fromListMatrix_ = fromListMatrix sing

----------------------
-- Matrix Instances --
----------------------

deriving instance (Eq (MatrixTF ns a)) => Eq (Matrix ns a)

deriving instance (Ord (MatrixTF ns a)) => Ord (Matrix ns a)

deriving instance (Show (MatrixTF ns a)) => Show (Matrix ns a)

instance SingI ns => Functor (Matrix ns) where
  fmap :: (a -> b) -> Matrix ns a -> Matrix ns b
  fmap = fmapSingMatrix sing

instance SingI ns => Data.Foldable.Foldable (Matrix ns) where
  foldr :: (a -> b -> b) -> b -> Matrix ns a -> b
  foldr comb b = Data.Foldable.foldr comb b . toListMatrix sing

  toList :: Matrix ns a -> [a]
  toList = toListMatrix sing

instance SingI ns => Distributive (Matrix ns) where
  distribute :: Functor f => f (Matrix ns a) -> Matrix ns (f a)
  distribute = distributeRep

instance SingI ns => Representable (Matrix ns) where
  type Rep (Matrix ns) = HList Fin ns

  tabulate :: (HList Fin ns -> a) -> Matrix ns a
  tabulate = genMatrix_

  index :: Matrix ns a -> HList Fin ns -> a
  index = flip indexMatrix

instance Num a => Num (Matrix '[] a) where
  Matrix a + Matrix b = Matrix (a + b)

  Matrix a * Matrix b = Matrix (a * b)

  Matrix a - Matrix b = Matrix (a - b)

  abs (Matrix a) = Matrix (abs a)

  signum (Matrix a) = Matrix (signum a)

  fromInteger :: Integer -> Matrix '[] a
  fromInteger = Matrix . fromInteger

instance SingI ns => Applicative (Matrix ns) where
  pure :: a -> Matrix ns a
  pure = pureRep

  (<*>) :: Matrix ns (a -> b) -> Matrix ns a -> Matrix ns b
  (<*>) = apRep

instance SingI ns => Monad (Matrix ns) where
  (>>=) :: Matrix ns a -> (a -> Matrix ns b) -> Matrix ns b
  (>>=) = bindRep
