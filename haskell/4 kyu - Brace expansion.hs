module Kata.BraceExpansion (expandBraces) where

import           Data.Maybe
import           Data.Foldable
import           Text.ParserCombinators.ReadP


data Expr
  = Empty
  | Str String
  | Braces [Expr]
  | Seq [Expr]
  deriving Show

data Mode = Comma | NoComma

strP :: Mode -> ReadP Expr
strP Comma   = fmap Str $ munch1 (`notElem` "{}")
strP NoComma = fmap Str $ munch1 (`notElem` ",{}")

bracesP :: ReadP Expr
bracesP = fmap Braces $ between (char '{') (char '}') $ sepBy1
  (pure Empty +++ exprP NoComma)
  (char ',')

seqP :: Mode -> ReadP Expr
seqP comma = fmap Seq $ many1 $ strP comma +++ bracesP

exprP :: Mode -> ReadP Expr
exprP comma = strP comma +++ bracesP +++ seqP comma

parseExpr :: String -> Expr
parseExpr = fst . fromJust . find (null . snd) . readP_to_S (exprP Comma)

expand :: [String] -> Expr -> [String]
expand rs e = case e of
  Empty     -> rs
  Str    s  -> map (<> s) rs
  Braces es -> concatMap (expand rs) es
  Seq    es -> foldl expand rs es

expandBraces :: String -> [String]
expandBraces "" = [""]
expandBraces s = expand [""] $ parseExpr s
