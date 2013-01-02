module Main where

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not deriving (Show)
data BinaryOp = And | Or deriving (Show)

data Expression = Bool Bool
                | UnaryExpr (UnaryOp, Expression)
                | BinaryExpr (BinaryOp, Expression, Expression)

------------------------------------------------------------------------------
-- Interpreter
------------------------------------------------------------------------------

operate_binary :: BinaryOp -> Bool -> Bool -> Bool
operate_binary And a b = a && b
operate_binary Or a b = a || b

operate_unary :: UnaryOp -> Bool -> Bool
operate_unary Not a = not a

solve :: Expression -> Bool
solve (Bool b) = b
solve (UnaryExpr (operation, a)) = operate_unary operation (solve a)
solve (BinaryExpr (operation, a, b)) = operate_binary operation (solve a) (solve b)

------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

expr1 :: Expression
expr1 = BinaryExpr (Or, Bool True, Bool False)

expr2 :: Expression
expr2 = BinaryExpr (And, Bool True, Bool False)

expr3 :: Expression
expr3 = BinaryExpr (And, expr1, expr2)

expr :: Expression
expr = UnaryExpr (Not, expr3)

main :: IO ()
main = print (solve expr)
