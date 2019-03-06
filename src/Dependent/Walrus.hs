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
import Dependent.Walrus.Matrix as X
import Dependent.Walrus.Peano as X
import Dependent.Walrus.Util as X
import Dependent.Walrus.Vec as X

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
