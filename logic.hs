{-# LANGUAGE ExistentialQuantification #-}

module Main where

import System.Environment
import System.Exit
import Control.Monad
import Control.Monad.Error

import Text.ParserCombinators.Parsec hiding (spaces)

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data Operation = And | Or deriving Show

data Expression = Bool Bool
                | Op (Operation, Expression, Expression)

------------------------------------------------------------------------------
-- Interpreter
------------------------------------------------------------------------------

operate :: Operation -> Bool -> Bool -> Bool
operate And a b = a && b
operate Or a b = a || b

solve :: Expression -> Bool
solve (Bool b) = b
solve (Op (operation, a, b)) = operate operation (solve a) (solve b)

------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

expr1 :: Expression
expr1 = Op (Or, Bool True, Bool False)

expr2 :: Expression
expr2 = Op (And, Bool True, Bool False)

expr :: Expression
expr = Op (And, expr1, expr2)

main :: IO ()
main = print (solve expr)
