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

module Dependent.Walrus.IFin where

import Data.Kind (Type)
import Data.Singletons.Prelude
import Data.Singletons.TH
import Text.Show (showParen, showString)

import Dependent.Walrus.Fin
import Dependent.Walrus.Peano

data IFin :: Peano -> Peano -> Type where
  IFZ :: forall (n :: Peano). IFin ('S n) 'Z
  IFS :: forall (n :: Peano) (m :: Peano). !(IFin n m) -> IFin ('S n) ('S m)

deriving instance Eq   (IFin x y)
deriving instance Ord  (IFin x y)
deriving instance Show (IFin x y)

toFinIFin :: IFin n m -> Fin n
toFinIFin IFZ = FZ
toFinIFin (IFS n) = FS (toFinIFin n)

toIntIFin :: IFin n m -> Int
toIntIFin = toIntFin . toFinIFin

-- | Create an 'IFin'.
--
-- >>> ifin (sing :: Sing N5) (sing :: Sing N2) :: IFin N5 N2
-- IFS (IFS IFZ)
ifin ::
     forall total n. ((n < total) ~ 'True)
  => Sing total
  -> Sing n
  -> IFin total n
ifin (SS _) SZ = IFZ
ifin (SS total') (SS n') =
  IFS $
    case ltSuccProof n' total' of
      Refl -> ifin total' n'
ifin _ _ = error "ifin: pattern impossible but GHC doesn't realize it"

-- | Create an 'IFin', but take the total implicitly.
--
-- >>> ifin_ @N5 (sing :: Sing N3) :: IFin N5 N3
-- IFS (IFS (IFS IFZ))
ifin_ ::
     forall total n. (SingI total, (n < total) ~ 'True)
  => Sing n
  -> IFin total n
ifin_ = ifin sing

data instance Sing (z :: IFin n m) where
  SIFZ :: Sing 'IFZ
  SIFS :: Sing x -> Sing ('IFS x)

instance SingI 'IFZ where
  sing = SIFZ

instance SingI n => SingI ('IFS n) where
  sing = SIFS sing

instance SingKind (IFin n m) where
  type Demote (IFin n m) = IFin n m
  fromSing :: forall (a :: IFin n m). Sing a -> IFin n m
  fromSing SIFZ = IFZ
  fromSing (SIFS fin') = IFS (fromSing fin')

  toSing :: IFin n m -> SomeSing (IFin n m)
  toSing IFZ = SomeSing SIFZ
  toSing (IFS fin') =
    case toSing fin' of
      SomeSing n -> SomeSing (SIFS n)

instance Show (Sing 'IFZ) where
  show SIFZ = "SIFZ"

instance Show (Sing n) => Show (Sing ('IFS n)) where
  showsPrec d (SIFS n) =
    showParen (d > 10) $
    showString "SIFS " . showsPrec 11 n
