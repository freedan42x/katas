{-# language TypeApplications #-}
module JSON.Parser (parse) where

import           JSON.Parser.Preloaded (Value(..))

import           Data.Char
import           Data.Foldable
import           Control.Monad
import           Text.ParserCombinators.ReadP


nullP :: ReadP Value
nullP = Null <$ string "null"

booleanP :: ReadP Value
booleanP = fmap (Boolean . (== "true")) $ string "true" +++ string "false"

stringP :: ReadP Value
stringP = fmap String $ between (char '"') (char '"') $ many $ satisfy (/= '"')

numberP :: ReadP Value
numberP = fmap (Number . read @Double) $ int +++ liftM2 (<>) int frac
 where
  digits      = many1 $ satisfy isDigit
  intUnsigned = choice
    [ fmap pure $ satisfy isDigit
    , liftM2 (:) (satisfy (\x -> x /= '0' && isDigit x)) digits
    ]
  int  = intUnsigned +++ liftM2 (:) (char '-') intUnsigned
  frac = liftM2 (:) (char '.') digits

arrayP :: ReadP Value
arrayP = fmap Array $ between (char '[') (char ']') $ skipSpaces *> sepBy
  (skipSpaces *> valueP <* skipSpaces)
  (char ',')

objectP :: ReadP Value
objectP = fmap Object $ between (char '{') (char '}') $ skipSpaces *> sepBy
  (  skipSpaces
  *> (liftM2 (,) stringP $ skipSpaces *> char ':' *> valueP)
  <* skipSpaces
  )
  (char ',')

valueP :: ReadP Value
valueP =
  skipSpaces *> choice [nullP, booleanP, stringP, numberP, arrayP, objectP] <* skipSpaces

parse :: String -> Maybe Value
parse = fmap fst . find (null . snd) . readP_to_S valueP
