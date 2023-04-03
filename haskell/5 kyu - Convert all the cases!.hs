{-# LANGUAGE LambdaCase #-}
module ConvertCase where

import           Data.Char
import           Data.Functor


data Case = Camel | Snake | Kebab deriving (Show, Eq)

getCase :: String -> Maybe Case
getCase = helper Nothing where
  helper :: Maybe Case -> String -> Maybe Case
  helper cs "" = cs
  helper cs (x : y : s)
    | isLower x && isUpper y && cs `elem` [Nothing, Just Camel] = helper
      (Just Camel)
      (dropWhile isUpper s)
    | isLower x && y == '_' && cs `elem` [Nothing, Just Snake] = helper
      (Just Snake)
      s
    | isLower x && y == '-' && cs `elem` [Nothing, Just Kebab] = helper
      (Just Kebab)
      s
  helper cs (x : s) | isLower x = helper cs s
                    | otherwise = Nothing

fromCamel :: String -> Case -> String
fromCamel s Camel = s
fromCamel s cs    = s >>= \case
  c | isUpper c -> (if cs == Snake then '_' else '-') : [toLower c]
    | otherwise -> [c]

fromSnake :: String -> Case -> String
fromSnake ""              = const ""
fromSnake r@('_' : y : s) = \case
  Snake    -> r
  cs@Camel -> toUpper y : fromSnake s cs
  cs@Kebab -> '-' : y : fromSnake s cs
fromSnake (x : s) = (x :) . fromSnake s

fromKebab :: String -> Case -> String
fromKebab ""              = const ""
fromKebab r@('-' : y : s) = \case
  Kebab    -> r
  cs@Camel -> toUpper y : fromKebab s cs
  cs@Snake -> '_' : y : fromKebab s cs
fromKebab (x : s) = (x :) . fromKebab s

changeCase :: String -> String -> Maybe String
changeCase "" _ = Just ""
changeCase s cs
  | Just cs <- lookup cs [("camel", Camel), ("snake", Snake), ("kebab", Kebab)]
  = if all isLower s
    then Just s
    else getCase s <&> \case
      Camel -> fromCamel s cs
      Snake -> fromSnake s cs
      Kebab -> fromKebab s cs
  | otherwise
  = Nothing
