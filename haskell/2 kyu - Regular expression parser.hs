module RegExpParser (RegExp(..),parseRegExp) where

import           Text.ParserCombinators.ReadP
import           Data.Foldable


data RegExp = Normal Char       -- ^ A character that is not in "()*|."
            | Any               -- ^ Any character
            | ZeroOrMore RegExp -- ^ Zero or more occurances of the same regexp
            | Or RegExp RegExp  -- ^ A choice between 2 regexps
            | Str [RegExp]      -- ^ A sequence of regexps.
            deriving (Show, Eq)

data Flag = NoZeroOrMore
          | NoOr
          | NoStr
          deriving Eq

parensP :: ReadP RegExp
parensP = between (char '(') (char ')') $ regexP []

normalP :: ReadP RegExp
normalP = Normal <$> satisfy (`notElem` "()*|.")

anyP :: ReadP RegExp
anyP = Any <$ char '.'

zeroOrMoreP :: ReadP RegExp
zeroOrMoreP =
  ZeroOrMore <$> (regexP [NoZeroOrMore, NoOr, NoStr] +++ parensP) <* char '*'

orP :: ReadP RegExp
orP = Or <$> (regexP [NoOr] <* char '|') <*> regexP [NoOr]

strP :: ReadP RegExp
strP = (\x xs -> Str (x : xs)) <$> e <*> many1 e
  where e = regexP [NoOr, NoStr]

regexP :: [Flag] -> ReadP RegExp
regexP flags = or' +++ str' +++ zeroOrMore' +++ parensP +++ normalP +++ anyP
 where
  or'         = if NoOr `elem` flags then pfail else orP
  zeroOrMore' = if NoZeroOrMore `elem` flags then pfail else zeroOrMoreP
  str'        = if NoStr `elem` flags then pfail else strP

parseRegExp :: String -> Maybe RegExp
parseRegExp s = fmap fst $ find (null . snd) $ readP_to_S (regexP []) s
