{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}


module Data.Range where

import Data.Bits
import Data.Word
import Test.QuickCheck (Property, (===), (.&&.), quickCheckAll)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import GHC.Exts (IsList(..))
import Control.Monad
import Data.Ratio
import System.Random
import Data.Semigroup


class (Eq a, Show a, Monoid a, Arbitrary a) => ARanges a where
  type RElem a :: *

  fromListR :: [RElem a] -> a

  fromListRN :: Int -> [RElem a] -> a

  toListR :: a -> [RElem a]

  insertR :: RElem a -> a -> a
  deleteR :: RElem a -> a -> a
  elemR  :: RElem a -> a -> Bool

  insertRange :: Range (RElem a) -> a -> a

  deleteRange :: Range (RElem a) -> a -> a



-- | Range of values, equivalent to @[a..b]@ with cases for @[]@, @[a..a]@, and @[a..a+b]@
data Range a = EmptyRange
             | Range  { fromRange    :: a
                      }
             | Range2 { fromRangeMin :: a
                      , fromRangeMax :: a
                      }
             deriving (Eq, Ord, Show, Functor)


instance Applicative Range where
  pure = Range

  EmptyRange <*> _ = EmptyRange
  _ <*> EmptyRange = EmptyRange
  Range f <*> x = f <$> x
  f <*> Range x = ($ x) <$> f
  Range2 fx fy <*> Range2 x y = Range2 (fx x) (fy y)



instance Ord a => Monoid (Range a) where
  mempty = EmptyRange

  mappend EmptyRange y = y
  mappend x EmptyRange = x
  mappend (Range x) (Range y) = case compare x y of
                                  LT -> Range2 x y
                                  EQ -> Range x
                                  GT -> Range2 y x
  mappend (Range x) (Range2 y y') = case compare x y of
                                      LT -> Range2 x y'
                                      EQ -> Range2 x y'
                                      GT -> case compare x y' of
                                              LT -> Range2 y y'
                                              EQ -> Range2 y y'
                                              GT -> Range2 y x

  mappend (Range2 x x') (Range y) = case compare y x of
                                      LT -> Range2 y x'
                                      EQ -> Range2 y x'
                                      GT -> case compare y x' of
                                              LT -> Range2 x x'
                                              EQ -> Range2 x x'
                                              GT -> Range2 x y

  mappend (Range2 x x') (Range2 y y') = case compare x y of
                                          LT -> Range2 x (max x' y')
                                          EQ -> Range2 x (max x' y')
                                          GT -> case compare x y' of
                                                  LT -> Range2 y (max x' y')
                                                  EQ -> Range2 y x'
                                                  GT -> Range2 y x'

instance Ord a => Semigroup (Range a)

instance Bits a => Bits (Range a) where
  EmptyRange .&. _ = EmptyRange
  _ .&. EmptyRange = EmptyRange
  Range x .&. Range y = Range (x .&. y)
  Range2 x x' .&. Range2 y y' = Range2 (x .&. y) (x' .&. y')
  Range x .&. Range2 y y' = Range2 (x .&. y) (x .&. y')
  Range2 x x' .&. Range y = Range2 (x .&. y) (x' .&. y)

  EmptyRange .|. y = y
  x .|. EmptyRange = x
  Range x .|. Range y = Range (x .|. y)
  Range2 x x' .|. Range2 y y' = Range2 (x .|. y) (x' .|. y')
  Range x .|. Range2 y y' = Range2 (x .|. y) (x .|. y')
  Range2 x x' .|. Range y = Range2 (x .|. y) (x' .|. y)

  xor EmptyRange y = y
  xor x EmptyRange = x
  xor (Range x) (Range y) = Range (xor x y)
  xor (Range2 x x') (Range2 y y') = Range2 (xor x y) (xor x' y')
  xor (Range x) (Range2 y y') = Range2 (xor x y) (xor x y')
  xor (Range2 x x') (Range y) = Range2 (xor x y) (xor x' y)

  complement EmptyRange = Range (complement zeroBits)
  complement (Range x) | x' == zeroBits = EmptyRange
                       | otherwise     = Range x'
    where
      x' = complement x
  complement (Range2 x y) | x' == zeroBits && y' == zeroBits = EmptyRange
                          | otherwise                     = Range2 x' y'
    where
      x' = complement x
      y' = complement y

  bitSizeMaybe x@EmptyRange = bitSizeMaybe (Range undefined `asTypeOf` x)
  bitSizeMaybe (Range x) = bitSizeMaybe x
  bitSizeMaybe (Range2 x _) = bitSizeMaybe x

  shift x 0 = x
  shift EmptyRange i | x' == zeroBits = EmptyRange
                     | otherwise    = Range x'
    where
      x' = shift zeroBits i
  shift (Range x) i | x' == zeroBits = EmptyRange
                    | otherwise     = Range x'
    where
      x' = shift x i
  shift (Range2 x y) i | x' == zeroBits && y' == zeroBits = EmptyRange
                       | otherwise     = Range2 x' y'
    where
      x' = shift x i
      y' = shift y i

  rotate x 0 = x
  rotate EmptyRange i | x' == zeroBits = EmptyRange
                      | otherwise    = Range x'
    where
      x' = rotate zeroBits i
  rotate (Range x) i | x' == zeroBits = EmptyRange
                    | otherwise     = Range x'
    where
      x' = rotate x i
  rotate (Range2 x y) i | x' == zeroBits && y' == zeroBits = EmptyRange
                        | otherwise     = Range2 x' y'
    where
      x' = rotate x i
      y' = rotate y i

  testBit EmptyRange _ = False
  testBit (Range x) i = testBit x i
  testBit (Range2 x y) i | i <= bitSize x = testBit x i
                         | otherwise   = testBit y (i - bitSize x)


  bit i | i <= bitSize x = Range (bit i)
        | otherwise     = Range2 zeroBits x
    where
      x = bit (i - bitSize x)

  isSigned EmptyRange = False
  isSigned (Range x) = isSigned x
  isSigned (Range2 x y) = isSigned x && isSigned y


  popCount EmptyRange = 0
  popCount (Range x) = popCount x
  popCount (Range2 x y) = popCount x + popCount y


instance FiniteBits a => FiniteBits (Range a) where
  finiteBitSize x@EmptyRange = finiteBitSize (Range undefined `asTypeOf` x)
  finiteBitSize (Range x) = finiteBitSize x
  finiteBitSize (Range2 x _) = finiteBitSize x


instance (Arbitrary a, Num a) => Arbitrary (Range a) where
  arbitrary = oneof [ return EmptyRange
                    , Range <$> arbitrary
                    , liftM2 (\x y -> Range2 x (x + abs y)) arbitrary arbitrary
                    ]



instance (Arbitrary a, Ord a, Num a, Enum a, Show a) => ARanges (Range a) where
  type RElem (Range a) = a

  fromListR = foldMap Range

  fromListRN _ = foldMap Range

  toListR = foldRange (:) []

  insertR x = mappend (Range x)

  deleteR _ EmptyRange = EmptyRange
  deleteR x (Range y)  | x == y     = EmptyRange
                       | otherwise = Range y

  deleteR x (Range2 y z) | x == y     = if y + 1 == z
                                           then Range z
                                           else Range2 (y + 1) z
                         | x == z     = if y + 1 == z
                                           then Range y
                                           else Range2 y (z - 1)
                         | otherwise = Range2 y z

  elemR _  EmptyRange   = False
  elemR x  (Range y   ) = x == y
  elemR x ~(Range2 y z) = y <= x && x <= z

  insertRange = mappend

  deleteRange = flip $ foldRange deleteR

-- | Minimum of a `Range`
minRange :: Range a -> Maybe a
minRange   EmptyRange  = Nothing
minRange  (Range  x  ) = Just x
minRange ~(Range2 x _) = Just x

-- | Maximum of a `Range`
maxRange :: Range a -> Maybe a
maxRange   EmptyRange  = Nothing
maxRange  (Range  x  ) = Just x
maxRange ~(Range2 _ y) = Just y

-- | Left-fold over the `Range`, using the type's `Enum` instance to provide
-- values between the endpoints
foldRange :: Enum a => (a -> b -> b) -> b -> Range a -> b
foldRange _ x EmptyRange = x
foldRange f x (Range y) = f y x
foldRange f x (Range2 y z) = foldr f x [y..z]

-- | Pretty-print a `Range` using the given method to `show` the endpoints
ppRangeWith :: (a -> String) -> Range a -> String
ppRangeWith _ EmptyRange = "[..]"
ppRangeWith p (Range x) = concat ["[", p x, "]"]
ppRangeWith p ~(Range2 x y) = concat ["[", p x, "..", p y, "]"]

