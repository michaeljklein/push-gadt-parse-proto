{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib where

import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Trans.Maybe
import Data.ByteString.UTF8 (replacement_char)
import Data.ByteString (ByteString, uncons)
import Data.Bits
import Data.Word
import Data.Range
import Control.Monad.Fail
import Prelude hiding (fail)
import Data.Coerce
import Data.Bifunctor
import Data.Foldable


-- Want:
-- - no char
--   * empty
--   * error
-- - char
--   * with non-empty range
--   * passed to function to update state: could error or continue

-- So, let's replace replacement_char with failure
-- and buncons with (_ :: m Char)

-- catMaybesCofree :: Cofree Maybe (Maybe a) -> Cofree Maybe a

-- catMaybeTsCofree :: Applicative m => Cofree (MaybeT m) (Maybe a) -> Cofree (MaybeT m) a



data Range1 a = Range1 { range1Min :: !a
                       , range1Max :: !a
                       } deriving (Eq, Ord, Show, Read)

data Ranged1 i a = Ranged1 { ranged1    :: !(Range1 i)
                           , ranged1Val :: !a
                           } deriving (Eq, Ord, Show, Functor)

instance Comonad (Ranged1 i) where
  extract ~(Ranged1 _ x) = x

  duplicate rd@(~(Ranged1 r _)) = Ranged1 r rd


-- | NOTE: These should be extended to utilize the fact that the resulting data structure is alternating
class Functor f => Push2 f g where
  push2 :: f (g a b) -> f (g (f a) (f b))
  push2 = pver2 . part2

  pver2 :: f (f (g a b)) -> f (g (f a) (f b))

  part2 :: f (g a b) -> f (f (g a b))

pushP2 :: Push2 f Either => (a -> Bool) -> f a -> f (Either (f a) (f a))
pushP2 p = push2 . fmap (\x -> if p x then Right x else Left x)

class (Functor f, Functor g) => Push f g where
  push :: f (g a) -> f (g (f a))
  push = pver . part

  part :: f (g a) -> f (f (g a))

  pver :: f (f (g a)) -> f (g (f a))

instance Push (Cofree Maybe) Maybe where
  part :: Cofree Maybe (Maybe a) -> Cofree Maybe (Cofree Maybe (Maybe a))
  part xss@(x :< xs) = case xs of
    Nothing -> xss :< Nothing
    ~(Just xs') -> case x of
      Nothing   -> case part xs' of
        (ys@(Nothing :< _) :< zs) -> (x :< Just ys) :< zs
        ys                        -> (x :< Nothing) :< Just ys
      ~(Just _) -> case part xs' of
        (ys@(Just _  :< _) :< zs) -> (x :< Just ys) :< zs
        ys                        -> (x :< Nothing) :< Just ys

  pver :: Cofree Maybe (Cofree Maybe (Maybe a)) -> Cofree Maybe (Maybe (Cofree Maybe a))
  pver = fmap pver'
    where pver' xs@(Nothing :< _) = Nothing
          pver' xs                = Just $ (\(~(Just x)) -> x) <$> xs

-- | `fmap` and `push`
pmap :: Push f g => (a -> g b) -> f a -> f (g (f b))
pmap f = push . fmap f

-- | `pmap` with a predicate
pmapP :: Push f Maybe => (a -> Bool) -> f a -> f (Maybe (f a))
pmapP p = pmap $ \x -> if p x
                          then Just x
                          else Nothing


instance Push2 (Cofree Maybe) Either where
  pver2 :: Cofree Maybe (Cofree Maybe (Either a b)) -> Cofree Maybe (Either (Cofree Maybe a) (Cofree Maybe b))
  pver2 = fmap pver2'
    where
      pver2' xs@(Left  _ :< _) = Left  $ (\(~(Left  x)) -> x) <$> xs
      pver2' xs                = Right $ (\(~(Right x)) -> x) <$> xs

  part2 :: Cofree Maybe (Either a b) -> Cofree Maybe (Cofree Maybe (Either a b))
  part2 xss@(~(x :< xs)) = case xs of
    Nothing     -> xss :< Nothing
    ~(Just xs') -> case x of
      Left _     -> case part2 xs' of
        (ys@(Left  _ :< _) :< zs) -> (x :< Just ys) :< zs
        ys                        -> (x :< Nothing) :< Just ys
      ~(Right _) -> case part2 xs' of
        (ys@(Right _ :< _) :< zs) -> (x :< Just ys) :< zs
        ys                        -> (x :< Nothing) :< Just ys

-- | `fmap` and `push2`
pmap2 :: Push2 f g => (a -> g b c) -> f a -> f (g (f b) (f c))
pmap2 f = push2 . fmap f

-- | `pmap2` with a predicate
pmapP2 :: Push2 f Either => (a -> Bool) -> f a -> f (Either (f a) (f a))
pmapP2 p = pmap2 $ \x -> if p x
                            then Right x
                            else Left  x


-- Want: inhabitance-typed GADTs with unfold, map, fold, etc.

-- GADT = (|) | (&) | (->) | Var | forall Var | (n : Nat)

-- def CamelCasedGADT a0 a1 a2 .. an
--   constructor0 : t0 -> t1 -> .. -> CamelCasedGADT a0 a1 a2 .. an
--   (symbolic) : s0 -> s1 -> .. -> CamelCasedGADT a0 a1 a2 .. an

-- def (symbolic) a0 a1 a2 .. an
--   ..

-- (<<) :: Monad m => m a -> m b -> m a
-- x << y = do
--   x' <- x
--   void $ y
--   return x'

-- parens :: Parser a -> Parser a
-- parens p = char '(' >> p << char ')'

-- parseCamelCased :: Parser ConstructorName
-- parseCamelCased = do
--   c <- peekChar
--   if isUpper c
--      then do
--        _


-- parseSymbolic :: Parser ConstructorName

-- parseConstructorName :: Parser ConstructorName
-- parseConstructorName = parseCamelCased <|> parens parseSymbolic

-- parseGADT :: Parser GADT
-- parseGADT = do
--   string "def "
--   name         <- parseConstructorName
--   args         <- sepBySpaces1 parseLowerCased
--   constructors <- indented1 $ do
--     constructorName <- parseConstructorName
--     string " : "
--     FunctionType xs <- parseType
--     (xs `endsWith`) $ do
--       void $ parseName name
--       mapM_ parseArg args
--     return $ Constructor constructorName xs
--   return $ GADT name args constructors

-- parseType :: Parser Type
-- parseType = do
--   forallVars <- parseMaybe $ do
--     string "forall "
--     sepBySpaces1 parseLowerCased << string "."
--   function' <- (`sepBy1` "->") $ do
--     product' <- (`sepBy1` "&") $ do
--       sum' <- (`sepBy1` "|") $ do
--         alt [ NatType    <$> parseNat
--             , VarType    <$> parseLowerCased
--             , ParensType <$> parens parseType
--             ]
--       return . ignoringSingleton SumType $ sum'
--     return . ignoringSingleton ProductType $ product'
--   return . ParsedType forallVars . ignoringSingleton FunctionType $ function'

-- ignoringSingleton :: (NonEmpty a -> a) -> NonEmpty a -> a
-- ignoringSingleton f (x :| []) = x
-- ignoringSingleton f xs        = f xs

