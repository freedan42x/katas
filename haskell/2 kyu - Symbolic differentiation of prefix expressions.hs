{-# LANGUAGE LambdaCase, TypeApplications #-}
module SymbolicDifferentiationOfPrefixExpressions (diff) where

import           Data.Char
import           Data.Maybe
import           Data.Foldable
import           Data.Bifunctor
import           Text.ParserCombinators.ReadP

data UnOp = Cos | Sin | Tan | Exp | Ln deriving Eq

data BinOp = Plus | Minus | Mult | Div | Pow deriving Eq

data Expr
  = Var
  | Lit Float
  | UnOp UnOp Expr
  | BinOp BinOp Expr Expr

unOps :: [(String, UnOp)]
unOps = [("cos", Cos), ("sin", Sin), ("tan", Tan), ("exp", Exp), ("ln", Ln)]

binOps :: [(String, BinOp)]
binOps = [("+", Plus), ("-", Minus), ("*", Mult), ("/", Div), ("^", Pow)]

instance Show UnOp where
  show s = fst $ fromJust $ find ((s ==) . snd) unOps

instance Show BinOp where
  show s = fst $ fromJust $ find ((s ==) . snd) binOps

instance Show Expr where
  show = \case
    Var            -> "x"
    Lit x -> let n = round x in if fromInteger n == x then show n else show x
    UnOp op e      -> concat ["(", show op, " ", show e, ")"]
    BinOp op e1 e2 -> concat ["(", show op, " ", show e1, " ", show e2, ")"]

ws1 :: ReadP ()
ws1 = skipMany1 $ satisfy isSpace

parens :: ReadP a -> ReadP a
parens = between (char '(') (char ')')

var :: ReadP Expr
var = Var <$ char 'x'

lit :: ReadP Expr
lit = readS_to_P $ \s -> first Lit <$> reads @Float s

unary :: ReadP Expr
unary = parens $ do
  s <- choice $ map (string . fst) unOps
  ws1
  e <- expr
  pure $ UnOp (fromJust $ lookup s unOps) e

binary :: ReadP Expr
binary = parens $ do
  s <- choice $ map (string . fst) binOps
  ws1
  e1 <- expr
  ws1
  e2 <- expr
  pure $ BinOp (fromJust $ lookup s binOps) e1 e2

expr :: ReadP Expr
expr = var +++ lit +++ unary +++ binary

parse :: String -> Expr
parse = fst . fromJust . find (null . snd) . readP_to_S expr

isConst :: Expr -> Bool
isConst = \case
  Lit _       -> True
  Var         -> False
  UnOp _ _    -> False
  BinOp _ x y -> isConst x && isConst y

applyBinOp :: BinOp -> Expr -> Expr -> Float
applyBinOp op (Lit x) (Lit y) = case op of
  Plus  -> x + y
  Minus -> x - y
  Mult  -> x * y
  Div   -> x / y
  Pow   -> x ** y
applyBinOp op (BinOp op' x y) e = applyBinOp op (Lit $ applyBinOp op' x y) e
applyBinOp op e (BinOp op' x y) = applyBinOp op e (Lit $ applyBinOp op' x y)
applyBinOp _ _ _ = error "expr is not a const"

reduce :: Expr -> Expr
reduce = \case
  Lit k -> Lit k
  Var   -> Var
  BinOp Plus x y | Lit 0 <- reduce x -> reduce y
                 | Lit 0 <- reduce y -> reduce x
  BinOp Mult x y | Lit 0 <- reduce x -> Lit 0
                 | Lit 0 <- reduce y -> Lit 0
                 | Lit 1 <- reduce x -> reduce y
                 | Lit 1 <- reduce y -> reduce x
                 | UnOp op e <- reduce x, Lit k <- reduce y -> BinOp Mult (Lit k) (UnOp op e)
                 | BinOp op a b <- reduce x, Lit k <- reduce y -> BinOp Mult (Lit k) (BinOp op a b)
  BinOp Pow x y | Lit 0 <- reduce y -> Lit 1
                | Lit 0 <- reduce x -> Lit 0
                | Lit 1 <- reduce y -> reduce x
                | Lit 1 <- reduce x -> Lit 1
  UnOp op e -> UnOp op $ reduce e
  BinOp op x y
    | isConst (reduce x) && isConst (reduce y) -> Lit
    $ applyBinOp op (reduce x) (reduce y)
    | otherwise -> BinOp op (reduce x) (reduce y)

derivUnrec :: Expr -> Expr
derivUnrec = \case
  UnOp Exp x -> UnOp Exp x
  UnOp Ln  x -> BinOp Div (Lit 1) x
  UnOp Sin x -> UnOp Cos x
  UnOp Cos x -> BinOp Mult (Lit (-1)) $ UnOp Sin x
  UnOp Tan x -> BinOp Plus (Lit 1) $ BinOp Pow (UnOp Tan x) (Lit 2)

deriv :: Expr -> Expr
deriv = \case
  Lit _                  -> Lit 0
  Var                    -> Lit 1
  BinOp Pow  Var (Lit k) -> BinOp Mult (Lit k) $ BinOp Pow Var (Lit $ k - 1)
  BinOp Plus f   g       -> BinOp Plus (deriv f) (deriv g)
  BinOp Minus f   g       -> BinOp Minus (deriv f) (deriv g)
  BinOp Mult f g ->
    BinOp Plus (BinOp Mult (deriv f) g) (BinOp Mult f (deriv g))
  BinOp Div f g -> BinOp
    Div
    (BinOp Minus (BinOp Mult (deriv f) g) (BinOp Mult f (deriv g)))
    (BinOp Pow g (Lit 2))
  UnOp f e -> BinOp Mult (derivUnrec $ UnOp f e) (deriv e)
  r        -> error $ "unhandled " <> show r

diff :: String -> String
diff = show . reduce . deriv . reduce . parse
