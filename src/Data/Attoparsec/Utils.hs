
module Data.Attoparsec.Utils where

import Data.Range
import Data.Attoparsec.Internal.Types


-- | Get the `State` of a `Parser`
parserState :: Parser i (State i)
parserState = Parser $ \t pos more lose _succ -> _succ t pos more t

-- | Always succeeds
parserPos :: Parser i Pos
parserPos = Parser $ \t pos more lose _succ -> _succ t pos more pos

-- | Parse with the range of `Pos`itions consumed.
--
-- For example:
--
-- @
--  λ> let someDecimals = parseRanged decimal `sepBy` skip (not . isDigit)
--  λ> (fmap . first . ppRangeWith) (show . fromPos) `<$>` parseOnly someDecimals "10 20 30 "
--  Right [("[0..2]",10),("[3..5]",20),("[6..8]",30)]
-- @
--
parseRanged :: Parser i a -> Parser i (Range Pos, a)
parseRanged p = do
  initalPos <- parserPos
  p'        <- p
  endPos    <- parserPos
  return (pure initalPos <> pure endPos, p')

