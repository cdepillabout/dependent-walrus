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

module Dependent.Walrus.Vec where

import Data.Distributive (Distributive(distribute))
import qualified Data.Foldable as Data.Foldable
import Data.Functor.Rep (Representable(..), apRep, bindRep, distributeRep, pureRep)
import Data.Kind (Type)
import Data.MonoTraversable (Element, MonoFoldable, MonoFunctor, MonoPointed)
import Data.Singletons.Prelude
import Data.Singletons.TH

import Dependent.Walrus.Fin (Fin(FS, FZ))
import Dependent.Walrus.IFin (IFin(IFS, IFZ))
import Dependent.Walrus.Peano (N1, Peano(S, Z), Sing(SS, SZ), SPeano)

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
