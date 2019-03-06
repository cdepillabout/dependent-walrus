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

module Dependent.Walrus.Peano where

import Data.Kind (Type)
import Data.Singletons.Prelude
import Data.Singletons.TH
import Unsafe.Coerce (unsafeCoerce)

$(singletons [d|

  data Peano = Z | S Peano deriving (Eq, Ord, Show)

  addPeano :: Peano -> Peano -> Peano
  addPeano Z a = a
  addPeano (S a) b = S (addPeano a b)

  subtractPeano :: Peano -> Peano -> Peano
  subtractPeano Z _ = Z
  subtractPeano a Z = a
  subtractPeano (S a) (S b) = subtractPeano a b

  multPeano :: Peano -> Peano -> Peano
  multPeano Z _ = Z
  multPeano (S a) b = addPeano (multPeano a b) b

  n0 :: Peano
  n0 = Z

  n1 :: Peano
  n1 = S n0

  n2 :: Peano
  n2 = S n1

  n3 :: Peano
  n3 = S n2

  n4 :: Peano
  n4 = S n3

  n5 :: Peano
  n5 = S n4

  n6 :: Peano
  n6 = S n5

  n7 :: Peano
  n7 = S n6

  n8 :: Peano
  n8 = S n7

  n9 :: Peano
  n9 = S n8

  n10 :: Peano
  n10 = S n9

  n24 :: Peano
  n24 = multPeano n4 n6

  instance Num Peano where
    (+) = addPeano

    (-) = subtractPeano

    (*) = multPeano

    abs = id

    signum Z = Z
    signum (S _) = S Z

    fromInteger n =
      if n < 0
        then error "Num Peano fromInteger: n is negative"
        else
          if n == 0 then Z else S (fromInteger (n - 1))

  instance Enum Peano where
    fromEnum Z = 0
    fromEnum (S n) = 1 + fromEnum n

    toEnum n
      | n < 0 = error "Enum Peano toEnum: n is negative"
      | n == 0 = Z
      | otherwise = S (toEnum (n - 1))
  |])

-- | This is a proof that if we know @'S' n@ is less than @'S' m@, then we
-- know @n@ is also less than @m@.
--
-- >>> ltSuccProof (sing :: Sing N4) (sing :: Sing N5)
-- Refl
ltSuccProof ::
     forall (n :: Peano) (m :: Peano) proxy. ('S n < 'S m) ~ 'True
  => proxy n
  -> proxy m
  -> (n < m) :~: 'True
ltSuccProof _ _ = unsafeCoerce (Refl :: Int :~: Int)

