{-# LANGUAGE DeriveFunctor, LambdaCase #-}
module ApplicativeParser where

import           Data.Char
import           Prelude                 hiding ( fmap )



-- | An ambiguous parser.
newtype Parser a = P { unP :: String -> [(String, a)] } deriving Functor

-- | Change the result of a parser.
pmap :: (a -> b) -> Parser a -> Parser b
pmap = (<$>)

-- | Operator version of 'pmap'.
(<#>) :: (a -> b) -> Parser a -> Parser b
(<#>) = pmap

-- | Parse a value and replace it.
(<#) :: a -> Parser b -> Parser a
(<#) = (<$)

infixl 4 <#>
infixl 4 <#

-- | Inject a value into an identity parser.
inject :: a -> Parser a
inject x = P $ \s -> [(s, x)]

-- | Given a parser with a function value and another parser, parse the function
-- first and then the value, return a parser which applies the function to the
-- value.
(<@>) :: Parser (a -> b) -> Parser a -> Parser b
pf <@> px = P $ \s -> [ (r, f a) | (s', f) <- unP pf s, (r, a) <- unP px s' ]

(<@) :: Parser a -> Parser b -> Parser a
pa <@ pb = const <#> pa <@> pb

(@>) :: Parser a -> Parser b -> Parser b
pa @> pb = id <# pa <@> pb

infixl 4 <@
infixl 4 @>
infixl 4 <@>


-- | Parse a character only when a predicate matches.
predP :: (Char -> Bool) -> Parser Char
predP p = P $ \case
  (x : xs) | p x -> [(xs, x)]
  _              -> []

-- | Succeed only when parsing the given character.
charP :: Char -> Parser Char
charP c = predP (c ==)

-- | Parse a whole string.
stringP :: String -> Parser String
stringP = foldr (\x r -> (:) <#> charP x <@> r) $ inject ""


-- | Construct a parser that never parses anything.
emptyP :: Parser a
emptyP = P $ const []

-- | Combine two parsers: When given an input, provide the results of both parser run on the input.
(<<>>) :: Parser a -> Parser a -> Parser a
p1 <<>> p2 = P $ (++) <$> unP p1 <*> unP p2

infixl 3 <<>>

-- | Apply the parser zero or more times.
many :: Parser a -> Parser [a]
many p = (:) <#> p <@> many p <<>> inject []

-- | Apply the parser one or more times.
some :: Parser a -> Parser [a]
some p = (:) <#> p <@> (some p <<>> inject [])


-- | Apply a parser and return all ambiguous results, but only those where the input was fully consumed.
runParser :: Parser a -> String -> [a]
runParser p = map snd . filter (("" ==) . fst) . unP p

-- | Apply a parser and only return a result, if there was only one unambiguous result with output fully consumed.
runParserUnique :: Parser a -> String -> Maybe a
runParserUnique p cs = case unP p cs of
  [("", r)] -> Just r
  _         -> Nothing


-- | Kinds of binary operators.
data BinOp = AddBO | MulBO deriving (Eq, Show)

-- | Some kind of arithmetic expression.
data Expr = ConstE Int
          | BinOpE BinOp Expr Expr
          | NegE Expr
          | ZeroE
          deriving (Eq, Show)

evalExpr :: Expr -> Int
evalExpr = \case
  ConstE n -> n
  BinOpE b e1 e2 ->
    (if b == AddBO then (+) else (*)) (evalExpr e1) (evalExpr e2)
  NegE e -> negate $ evalExpr e
  ZeroE  -> 0


constP :: Parser Expr
constP = ConstE . digitToInt <#> predP isDigit

plusP :: Parser Expr
plusP =
  BinOpE AddBO <#> (exprP <@ charP ' ' <@ charP '+') <@> (charP ' ' @> exprP)

mulP :: Parser Expr
mulP =
  BinOpE MulBO <#> (exprP <@ charP ' ' <@ charP '*') <@> (charP ' ' @> exprP)

negP :: Parser Expr
negP = NegE <#> (charP '-' @> exprP)

zeroP :: Parser Expr
zeroP = ZeroE <# charP 'z'

exprP :: Parser Expr
exprP =
  zeroP <<>> constP <<>> negP <<>> (charP '(' @> (plusP <<>> mulP) <@ charP ')')

-- | Parse arithmetic expressions, with the following grammar:
--
--     expr         ::= const | binOpExpr | neg | zero
--     const        ::= int
--     binOpExpr    ::= '(' expr ' ' binOp ' ' expr ')'
--     binOp        ::= '+' | '*'
--     neg          ::= '-' expr
--     zero         ::= 'z'
--
parseExpr :: String -> Maybe Expr
parseExpr = runParserUnique exprP
