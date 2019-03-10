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

module Dependent.Walrus.Matrix where

import Data.Distributive (Distributive(distribute))
import Data.Foldable (foldl')
import qualified Data.Foldable as Data.Foldable
import Data.Functor.Rep (Representable(..), apRep, bindRep, distributeRep, pureRep)
import Data.Kind (Type)
import Data.MonoTraversable (Element, MonoFoldable, MonoFunctor, MonoPointed)
import Data.Singletons.Prelude
import Data.Singletons.TH

import Dependent.Walrus.Fin (Fin(FS, FZ))
import Dependent.Walrus.HList (HList(EmptyHList, (:<)), pattern ConsHList)
import Dependent.Walrus.IFin (IFin(IFS, IFZ))
import Dependent.Walrus.Peano (N1, Peano(S, Z), Sing(SS, SZ), SPeano)
import Dependent.Walrus.Util (doubletonList, singletonList)
import Dependent.Walrus.Vec
  ( Vec((:*), EmptyVec)
  , pattern ConsVec
  , fromListLeftOverVec
  , fromListVec
  , genVec
  , imapVec
  , indexVec
  , singletonVec
  , updateAtVec
  , zipWithVec
  )

-- $setup
-- >>> import Dependent.Walrus.Fin (toIntFin)
-- >>> import Dependent.Walrus.Peano (N0, N1, N2, N3, N7, N9)

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
-- >>> multMatrix (sing @N3) (sing @N0) (sing @N2) mat1 mat2
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
-- >>> multMatrix (sing @N2) (sing @N3) (sing @N2) mat1 mat2
-- Matrix {unMatrix = (58 :* (64 :* EmptyVec)) :* ((139 :* (154 :* EmptyVec)) :* EmptyVec)}
multMatrix
  :: forall n m o a
   . Num a
  => Sing n
  -> Sing m
  -> Sing o
  -> Matrix '[n, m] a
  -> Matrix '[m, o] a
  -> Matrix '[n, o] a
multMatrix n SZ o _ _ = replicateMatrix (doubletonList n o) 0
multMatrix n m o mat1 mat2 = genMatrix (doubletonList n o) go
  where
    go :: HList Fin '[n, o] -> a
    go (finN :< finO :< EmptyHList) =
      let rowVec = getRowMatrix finN mat1
          colVec = getColMatrix finO mat2
      in sum $ zipWithVec (*) rowVec colVec

dotProdMatrix :: Matrix '[n, m] a -> Vec m a -> Vec n a
dotProdMatrix mat vec = undefined

-- | Convert a 'Matrix' with only one row to a 'Vec'.
--
-- >>> let Just mat = fromListMatrix (sing @'[N1, N3]) [1..3]
-- >>> mat
-- Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* EmptyVec}
--
-- >>> rowMatrixToVec mat
-- 1 :* (2 :* (3 :* EmptyVec))
rowMatrixToVec :: Matrix '[N1, x] a -> Vec x a
rowMatrixToVec = getRowMatrix FZ

-- | Convert a 'Vec' to a 'Matrix' with a single row.
--
-- >>> let Just vec = fromListVec (sing @N3) [1,2,3]
-- >>> vec
-- 1 :* (2 :* (3 :* EmptyVec))
--
-- >>> vecToRowMatrix vec
-- Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* EmptyVec}
vecToRowMatrix :: Vec x a -> Matrix '[N1, x] a
vecToRowMatrix v = Matrix $ fmap Only v :* EmptyVec

-- | Convert a 'Vec' to a 'Matrix' with a single column.
--
-- >>> let Just vec = fromListVec (sing @N3) [1,2,3]
-- >>> vec
-- 1 :* (2 :* (3 :* EmptyVec))
--
-- >>> vecToColMatrix vec
-- Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* EmptyVec}
vecToColMatrix :: Vec x a -> Matrix '[x, N1] a
vecToColMatrix v = Matrix $ fmap singletonVec v

-- | Convert a 'Matrix' with only one column to a 'Vec'.
--
-- >>> let Just mat = fromListMatrix (sing @'[N3, N1]) [1..3]
-- >>> mat
-- Matrix {unMatrix = (1 :* EmptyVec) :* ((2 :* EmptyVec) :* ((3 :* EmptyVec) :* EmptyVec))}
--
-- >>> colMatrixToVec mat
-- 1 :* (2 :* (3 :* EmptyVec))
colMatrixToVec :: Matrix '[x, N1] a -> Vec x a
colMatrixToVec = getColMatrix FZ

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
--
-- >>> fromListMatrix (sing @'[N2, N3]) [1..6]
-- Just (Matrix {unMatrix = (1 :* (2 :* (3 :* EmptyVec))) :* ((4 :* (5 :* (6 :* EmptyVec))) :* EmptyVec)})
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
