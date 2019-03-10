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

module Dependent.Walrus.Util where

import Data.Singletons.Prelude

-- | A @singleton@ function for type-level lists.
--
-- >>> singletonList (sing @'True)
-- SCons STrue SNil
singletonList :: forall x. Sing x -> Sing '[x]
singletonList x = SCons x SNil

-- | A function like 'singletonList', but creates a list with two elements.
--
-- >>> doubletonList (sing @'True) (sing @'False)
-- SCons STrue (SCons SFalse SNil)
doubletonList :: Sing x -> Sing y -> Sing '[x, y]
doubletonList x y = singletonList x %++ singletonList y
