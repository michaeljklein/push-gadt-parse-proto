# push-gadt-parse-proto

Prototypes for parsing GADTs in Flock using:
- [Attoparsec](hackage.haskell.org/package/attoparsec)
  + Input position ranges
- An implementation of `Data.Range`
- `Push` and `Push2`


## Data.Attoparsec.Utils

- Use `Parser` state and position to parse with a `Range` of input:

```haskell
parseRanged :: Parser i a -> Parser i (Range Pos, a)
```


## Data.Range

- Possibly empty ranges
- `ARanges` class, instance for easier testing
- `Monoid` and `Bits` instances


## Lib

- Non-empty ranges
- `Push` and `Push2`
  + `instance Push (Cofree Maybe) Maybe`
  + `instance Push2 (Cofree Maybe) Either`
- Commented notes on using the above to parse GADTs


# Docs

Haddock generated documentation may be found [here](https://michaeljklein.github.io/push-gadt-parse-proto/)

