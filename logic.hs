module Main where

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not
data BinaryOp = And | Or
type Variable = Char

data Expression = Bool Bool
                | Variable Variable
                | UnaryExpr (UnaryOp, Expression)
                | BinaryExpr (BinaryOp, Expression, Expression)

instance Show UnaryOp where
    show _ = "not"

instance Show BinaryOp where
    show And = "and"
    show Or = "or"

instance Show Expression where
    show (Bool b) = show b
    show (Variable v) = show v
    show (UnaryExpr (op, expr)) = concat ["(", show op, " ", show expr, ")"]
    show (BinaryExpr (op, expr1, expr2)) = concat ["(", show expr1, " ",
                                                   show op, " ", show expr2, ")"]

------------------------------------------------------------------------------
-- Interpreter
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

expr1 :: Expression
expr1 = BinaryExpr (Or, Bool True, (UnaryExpr (Not, (Bool False))))

expr2 :: Expression
expr2 = BinaryExpr (And, Bool True, Bool False)

expr3 :: Expression
expr3 = BinaryExpr (And, expr1, expr2)

expr :: Expression
expr = UnaryExpr (Not, expr3)

main :: IO ()
main = print expr
