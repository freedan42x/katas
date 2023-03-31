{-# LANGUAGE LambdaCase #-}
module SimpleInteractiveInterpreter where

import           Data.Char
import           Data.Maybe
import           Data.Foldable
import           Data.Bifunctor
import qualified Data.Map                      as M

import           Control.Applicative            ( (<|>) )
import           Control.Monad

import           Text.ParserCombinators.ReadP


data BinOp
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  deriving Show

data Expr
  = Lit Int
  | Ident String
  | Negate Expr
  | BinOp BinOp Expr Expr
  | Let String Expr
  | LetFun String [String] Expr
  | FunApp String [Expr]
  deriving Show

litP :: ReadP Expr
litP = fmap (Lit . read) $ munch1 isDigit

identP :: ReadP String
identP = (:) <$> satisfy isAlpha <*> munch (\c -> isAlpha c || isDigit c)

negateP :: Interpreter -> ReadP Expr
negateP interp = do
  char '-'
  skipSpaces
  e <- exprP interp
  pure $ Negate e

factorP :: Interpreter -> ReadP Expr
factorP interp = choice
  [ between (char '(') (char ')') $ exprP interp
  , litP
  , fmap Ident identP
  , negateP interp
  ]

binopP :: ReadP Expr -> [(Char, BinOp)] -> ReadP Expr
binopP factor ops = do
  x  <- factor
  ys <- many $ choice $ map
    (\(c, op) -> do
      skipSpaces
      char c
      skipSpaces
      y <- factor
      pure (y, op)
    )
    ops
  pure $ foldl (\a (b, op) -> BinOp op a b) x ys

-- factor ('*'|'/'|'%' factor)*
mulP :: Interpreter -> ReadP Expr
mulP interp = binopP (factorP interp) [('*', Mul), ('/', Div), ('%', Mod)]

-- mul ('+'|'-' mul)*
addP :: Interpreter -> ReadP Expr
addP interp = binopP (mulP interp) [('+', Add), ('-', Sub)]

letP :: Interpreter -> ReadP Expr
letP interp = do
  s <- identP
  skipSpaces
  char '='
  skipSpaces
  e <- letP interp +++ addP interp
  pure $ Let s e

letfP :: Interpreter -> ReadP Expr
letfP interp = do
  string "fn"
  skipSpaces
  name <- identP
  skipSpaces
  args <- many $ identP <* skipSpaces
  string "=>"
  skipSpaces
  body <- addP interp
  pure $ LetFun name args body

funappP :: Interpreter -> ReadP Expr
funappP interp = do
  name <- identP
  case M.lookup name $ funs interp of
    Just (args, _) ->
      fmap (FunApp name)
        $  replicateM (length args)
        $  skipSpaces
        *> (funappP interp +++ addP interp)
    _ -> pfail

exprP :: Interpreter -> ReadP Expr
exprP interp = letfP interp +++ letP interp +++ addP interp +++ funappP interp

data Interpreter
  = Interpreter { vars :: M.Map String Int
                , funs :: M.Map String ([String], Expr)
                }
    deriving Show

newInterpreter :: Interpreter
newInterpreter = Interpreter M.empty M.empty

applyBinOp :: BinOp -> Int -> Int -> Int
applyBinOp = \case
  Add -> (+)
  Sub -> (-)
  Mul -> (*)
  Div -> div
  Mod -> mod

funInvalid :: [String] -> Expr -> Maybe String
funInvalid vs = \case
  Lit    _    -> Nothing
  Ident  s    -> if s `elem` vs then Nothing else Just s
  Negate e    -> funInvalid vs e
  BinOp _ a b -> funInvalid vs a <|> funInvalid vs b
  _           -> error "unreachable"


subst :: [(String, Int)] -> Expr -> Expr
subst vs = \case
  Lit    x     -> Lit x
  Ident  s     -> Lit $ fromJust $ lookup s vs
  Negate e     -> Negate $ subst vs e
  BinOp op a b -> BinOp op (subst vs a) (subst vs b)
  _            -> error "unreachable"

interpret :: Expr -> Interpreter -> Either String (Result, Interpreter)
interpret e interp = case e of
  Lit x -> pure (Just x, interp)

  Ident s -> case M.lookup s $ vars interp of
    Just x -> Right (Just x, interp)
    _      -> case M.lookup s $ funs interp of
      Just ([], e) -> interpret e interp
      _            -> Left $ "No identifier `" <> s <> "`"

  Negate e ->
    fmap ((\(r, interp) -> (fmap negate r, interp))) $ interpret e interp

  BinOp op a b -> interpret a interp >>= \case
    (Just x, interp) -> interpret b interp >>= \case
      (Just y, interp) -> pure (Just $ applyBinOp op x y, interp)
      t                -> Right t
    t -> Right t

  Let s e -> if M.member s $ funs interp
    then Left $ "Identifier `" <> s <> "` is already taken for function"
    else interpret e interp >>= \case
      (Just x, interp) ->
        pure (Just x, interp { vars = M.insert s x $ vars interp })
      t -> Right t

  LetFun name args body -> if M.member name $ vars interp
    then Left $ "Identifier `" <> name <> "` is already taken for variable"
    else case funInvalid args body of
      Just s -> Left $ "Unknown identifier `" <> s <> "`"
      _      -> pure
        (Nothing, interp { funs = M.insert name (args, body) $ funs interp })

  FunApp s args -> case M.lookup s $ funs interp of
    Just (vs, e) -> if length args /= length vs
      then
        Left
        $  "Wrong amount of arguments: "
        <> show (length args)
        <> "("
        <> show args
        <> ") "
        <> show (length vs)
      else
        case
          foldl
            (\r arg -> case r of
              Right (rs, interp) -> case interpret arg interp of
                Right (Just r, interp) -> Right (r : rs, interp)
                Left  s                -> Left s
              Left t -> Left t
            )
            (Right ([], interp))
            args
        of
          Right (args, interp) -> interpret (subst (zip vs args) e) interp
          Left  s              -> Left s
    _ -> Left $ "No such function `" <> s <> "`"

type Result = Maybe Int

input :: String -> Interpreter -> Either String (Result, Interpreter)
input s interp = if null $ dropWhile isSpace s
  then Right (Nothing, interp)
  else case find (null . snd) $ readP_to_S (exprP interp) s of
    Just (e, _) -> interpret e interp
    _           -> Left "Invalid expression"
