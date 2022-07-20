module SimpleAssembler
  ( simpleAssembler
  )
where

import qualified Data.Map.Strict               as M
import           Text.Read


type Register = String
type Registers = M.Map String Int

data Value = Lit Int
           | Reg Register

data Instr = Mov Register Value
         | Inc Register
         | Dec Register
         | Jnz Value Value

evalValue :: Value -> Registers -> Int
evalValue (Lit x  ) _    = x
evalValue (Reg reg) regs = case M.lookup reg regs of
  Just x -> x
  _      -> error "Oopsie!"

evalInstrs :: [Instr] -> Registers
evalInstrs instrs = helper 0 M.empty where
  helper :: Int -> Registers -> Registers
  helper curLine regs
    | curLine >= length instrs = regs
    | otherwise = case instrs !! curLine of
      Mov reg x -> helper (curLine + 1) $ M.insert reg (evalValue x regs) regs
      Inc reg   -> helper (curLine + 1) $ M.adjust (+ 1) reg regs
      Dec reg   -> helper (curLine + 1) $ M.adjust (subtract 1) reg regs
      Jnz x y   -> if evalValue x regs /= 0
        then helper (curLine + evalValue y regs) regs
        else helper (curLine + 1) regs

parseValue :: String -> Value
parseValue s = case readMaybe s :: Maybe Int of
  Just x -> Lit x
  _      -> Reg s

parseInstr :: String -> Instr
parseInstr s = case words s of
  ["mov", reg, x] -> Mov reg $ parseValue x
  ["inc", reg]    -> Inc reg
  ["dec", reg]    -> Dec reg
  ["jnz", x, y]   -> Jnz (parseValue x) (parseValue y)
  _               -> error "Oopsie!"

simpleAssembler :: [String] -> Registers
simpleAssembler = evalInstrs . map parseInstr
