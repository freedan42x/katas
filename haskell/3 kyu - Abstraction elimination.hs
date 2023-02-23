{-# LANGUAGE LambdaCase #-}
module AbstractionElimination (eliminate) where

import           Text.ParserCombinators.ReadP
import           Data.Char                      ( isAsciiLower )
import           Data.Foldable


data SKI = S | K | I deriving Show

data LExpr
  = LVar Char
  | LAbs Char LExpr
  | LApp LExpr LExpr
  | LSKI SKI

instance Show LExpr where
  show = \case
    LVar c   -> [c]
    LAbs c e -> concat ["(λ", c : ".", show e, ")"]
    LApp u v -> concat ["(", show u, show v, ")"]
    LSKI t   -> show t

convert :: LExpr -> LExpr
convert = \case
  LAbs x (LVar y) | x == y    -> LSKI I
                  | otherwise -> LApp (LSKI K) (LVar y)
  LAbs x (LApp u v) ->
    LApp (LApp (LSKI S) $ convert $ LAbs x u) (convert $ LAbs x v)
  LAbs x (LAbs y e) -> convert $ LAbs x $ convert $ LAbs y e
  LAbs x (LSKI t  ) -> LApp (LSKI K) (LSKI t)

parseLVar :: ReadP LExpr
parseLVar = LVar <$> satisfy isAsciiLower

parseLAbs :: ReadP LExpr
parseLAbs = do
  char 'λ'
  cs <- many1 $ satisfy isAsciiLower
  char '.'
  e <- parseLExpr
  let go [x     ] = LAbs x e
      go (x : xs) = LAbs x $ go xs
  pure $ go cs

parseLApp :: ReadP LExpr
parseLApp = do
  e  <- parseLVar +++ between (char '(') (char ')') parseLExpr
  es <- many1 parseLExpr
  let go [x     ] = LApp e x
      go (x : xs) = LApp (go xs) x
  pure $ go $ reverse es

parseLExpr :: ReadP LExpr
parseLExpr = between (char '(') (char ')') p +++ p
  where p = parseLVar +++ parseLAbs +++ parseLApp

parseLExpr' :: String -> LExpr
parseLExpr' s = case find (\(_, e) -> null e) $ readP_to_S parseLExpr s of
  Just (e, _) -> e
  Nothing     -> error "wrong input"

eliminate :: String -> String
eliminate = show . convert . parseLExpr'
