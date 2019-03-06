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

module Dependent.Walrus.HList where

import Data.Kind (Type)

data HList :: (k -> Type) -> [k] -> Type where
  EmptyHList :: HList f '[]
  (:<) :: forall (f :: k -> Type) (a :: k) (as :: [k]). f a -> HList f as -> HList f (a ': as)

infixr 6 :<

-- | Data constructor for ':<'.
pattern ConsHList :: (f a :: Type) -> HList f as -> HList f (a ': as)
pattern ConsHList fa hlist = fa :< hlist
