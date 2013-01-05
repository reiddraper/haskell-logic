module Main where
import Control.Monad (replicateM)
import qualified Data.Map as Map
import qualified Data.Set as Set

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not
data BinaryOp = And | Or
newtype Variable = Var Char deriving (Eq, Ord)

data Expression = Bool Bool
                | Variable Variable
                | UnaryExpr (UnaryOp, Expression)
                | BinaryExpr (BinaryOp, Expression, Expression)

instance Show UnaryOp where
    show _ = "not"

instance Show BinaryOp where
    show And = "and"
    show Or = "or"

instance Show Variable where
    show (Var c) = [c]

instance Show Expression where
    show (Bool b) = show b
    show (Variable v) = show v
    show (UnaryExpr (op, expr)) = concat ["(", show op, " ", show expr, ")"]
    show (BinaryExpr (op, expr1, expr2)) = concat ["(", show expr1, " ",
                                                   show op, " ", show expr2, ")"]

type Mapping = Map.Map Variable Bool

------------------------------------------------------------------------------
-- Truth table
------------------------------------------------------------------------------

truthTable :: Expression -> [Bool]
truthTable expr = map (solveWithMapping expr) $ mappings expr

solveWithMapping :: Expression -> Mapping -> Bool
solveWithMapping expr mapping = solve (replace expr mapping)

replace :: Expression -> Mapping -> Expression
replace s@(Bool _) _ = s
replace (Variable v) m = Bool (Map.findWithDefault True v m)
replace (UnaryExpr (op, expr)) m = UnaryExpr (op, replace expr m)
replace (BinaryExpr (op, expr1, expr2)) m = BinaryExpr (op, (replace expr1 m), (replace expr2 m))

mappings :: Expression -> [Mapping]
mappings expr = let vs = Set.toList $ variables expr Set.empty
                    tfs = replicateM (length vs) [True, False]
                in map (Map.fromList . zip vs) tfs

variables :: Expression -> Set.Set Variable -> Set.Set Variable
variables (Bool _) s = s
variables (Variable v) s = Set.insert v s
variables (UnaryExpr (op, expr)) s = variables expr s
variables (BinaryExpr (op, expr1, expr2)) s = Set.union (variables expr1 s) (variables expr2 s)

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
expr1 = BinaryExpr (Or, Variable (Var 'A'), (UnaryExpr (Not, Variable (Var 'B'))))

expr2 :: Expression
expr2 = BinaryExpr (And, Variable (Var 'A'), Variable (Var 'B'))

expr3 :: Expression
expr3 = BinaryExpr (And, expr1, expr2)

expr :: Expression
expr = UnaryExpr (Not, expr3)

main :: IO ()
main = print $ truthTable expr
