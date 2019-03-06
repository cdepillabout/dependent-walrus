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

module Dependent.Walrus.Fin where

import Data.Kind (Type)
import Data.Singletons.Prelude
import Data.Singletons.TH
import Text.Show (showParen, showString)
import Unsafe.Coerce (unsafeCoerce)

import Dependent.Walrus.Peano

data Fin :: Peano -> Type where
  FZ :: forall (n :: Peano). Fin ('S n)
  FS :: forall (n :: Peano). !(Fin n) -> Fin ('S n)

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)
deriving instance Show (Fin n)

toIntFin :: Fin n -> Int
toIntFin FZ = 0
toIntFin (FS x) = succ $ toIntFin x

-- | Similar to 'ifin' but for 'Fin'.
--
-- >>> fin (sing :: Sing N5) (sing :: Sing N1) :: Fin N5
-- FS FZ
fin ::
     forall total n. ((n < total) ~ 'True)
  => Sing total
  -> Sing n
  -> Fin total
fin (SS _) SZ = FZ
fin (SS total') (SS n') =
  FS $
    case ltSuccProof n' total' of
      Refl -> fin total' n'
fin _ _ = error "fin: pattern impossible but GHC doesn't realize it"

-- | Similar to 'ifin_' but for 'Fin'.
--
-- >>> fin_ @N4 (sing :: Sing N2) :: Fin N4
-- FS (FS FZ)
fin_ ::
     forall total n. (SingI total, (n < total) ~ 'True)
  => Sing n
  -> Fin total
fin_ = fin sing

data instance Sing (z :: Fin n) where
  SFZ :: Sing 'FZ
  SFS :: Sing x -> Sing ('FS x)

instance SingI 'FZ where
  sing = SFZ

instance SingI n => SingI ('FS n) where
  sing = SFS sing

instance SingKind (Fin n) where
  type Demote (Fin n) = Fin n
  fromSing :: forall (a :: Fin n). Sing a -> Fin n
  fromSing SFZ = FZ
  fromSing (SFS fin') = FS (fromSing fin')

  toSing :: Fin n -> SomeSing (Fin n)
  toSing FZ = SomeSing SFZ
  toSing (FS fin') =
    case toSing fin' of
      SomeSing n -> SomeSing (SFS n)

instance Show (Sing 'FZ) where
  show SFZ = "SFZ"

instance Show (Sing n) => Show (Sing ('FS n)) where
  showsPrec d (SFS n) =
    showParen (d > 10) $
    showString "SFS " . showsPrec 11 n
