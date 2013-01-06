module Main where
import Control.Monad (replicateM)
import Data.Monoid
import Data.Foldable (Foldable, foldMap)
import qualified Data.Map as Map
import qualified Data.Set as Set

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not
data BinaryOp = And | Or
newtype Variable = Var Char deriving (Eq, Ord)

data Expression a = Leaf a
                    | UnaryExpr (UnaryOp, Expression a)
                    | BinaryExpr (BinaryOp, Expression a, Expression a)

instance Show UnaryOp where
    show _ = "not"

instance Show BinaryOp where
    show And = "and"
    show Or = "or"

instance Show Variable where
    show (Var c) = [c]

instance Show a => Show (Expression a) where
    show (Leaf l) = show l
    show (UnaryExpr (op, expr)) = concat ["(", show op, " ", show expr, ")"]
    show (BinaryExpr (op, expr1, expr2)) = concat ["(", show expr1, " ",
                                                   show op, " ", show expr2, ")"]

instance Foldable Expression where
    foldMap f (Leaf v) = f v
    foldMap f (UnaryExpr (_, expr)) = foldMap f expr
    foldMap f (BinaryExpr (_, expr1, expr2)) = (foldMap f expr1) `mappend` (foldMap f expr2)

type Mapping = Map.Map Variable Bool
type VarExpr = Expression Variable

------------------------------------------------------------------------------
-- Truth table
------------------------------------------------------------------------------

truthTable :: VarExpr -> [Bool]
truthTable expr = map (solveWithMapping expr) $ mappings expr

solveWithMapping :: VarExpr -> Mapping -> Bool
solveWithMapping expr mapping = solve (replace expr mapping)

replace :: VarExpr -> Mapping -> Expression Bool
replace (Leaf v) m = Leaf (Map.findWithDefault True v m)
replace (UnaryExpr (op, expr)) m = UnaryExpr (op, replace expr m)
replace (BinaryExpr (op, expr1, expr2)) m = BinaryExpr (op, (replace expr1 m), (replace expr2 m))

mappings :: VarExpr -> [Mapping]
mappings expr = let vs = Set.toList $ variables expr
                    tfs = replicateM (length vs) [True, False]
                in map (Map.fromList . zip vs) tfs

variables :: VarExpr -> Set.Set Variable
variables = foldMap Set.singleton

------------------------------------------------------------------------------
-- Interpreter
------------------------------------------------------------------------------

operate_binary :: BinaryOp -> Bool -> Bool -> Bool
operate_binary And a b = a && b
operate_binary Or a b = a || b

operate_unary :: UnaryOp -> Bool -> Bool
operate_unary Not a = not a

solve :: Expression Bool -> Bool
solve (Leaf b) = b
solve (UnaryExpr (operation, a)) = operate_unary operation (solve a)
solve (BinaryExpr (operation, a, b)) = operate_binary operation (solve a) (solve b)

------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

expr1 :: VarExpr
expr1 = BinaryExpr (Or, Leaf (Var 'A'), (UnaryExpr (Not, Leaf (Var 'B'))))

expr2 :: VarExpr
expr2 = BinaryExpr (And, Leaf (Var 'A'), Leaf (Var 'B'))

expr3 :: VarExpr
expr3 = BinaryExpr (And, expr1, expr2)

expr :: VarExpr
expr = UnaryExpr (Not, expr3)

main :: IO ()
main = print $ truthTable expr
