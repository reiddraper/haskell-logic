module Logic where
import Control.Monad (replicateM, liftM, liftM2, liftM3)
import Data.Monoid
import Data.Foldable (Foldable, foldMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.QuickCheck

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not
data BinaryOp = And | Or
newtype Variable = Var Char deriving (Eq, Ord)

data Expression a = Leaf a
                    | UnaryExpr UnaryOp (Expression a)
                    | BinaryExpr BinaryOp (Expression a) (Expression a)

instance Show UnaryOp where
    show _ = "not"

instance Show BinaryOp where
    show And = "and"
    show Or = "or"

instance Show Variable where
    show (Var c) = [c]

instance Show a => Show (Expression a) where
    show (Leaf l) = show l
    show (UnaryExpr op expr) = concat ["(", show op, " ", show expr, ")"]
    show (BinaryExpr op expr1 expr2) = concat ["(", show expr1, " ",
                                               show op, " ", show expr2, ")"]

instance Foldable Expression where
    foldMap f (Leaf v) = f v
    foldMap f (UnaryExpr _ expr) = foldMap f expr
    foldMap f (BinaryExpr _ expr1 expr2) = foldMap f expr1 `mappend` foldMap f expr2

instance Arbitrary UnaryOp where
    arbitrary = return Not

instance Arbitrary BinaryOp where
    arbitrary = oneof [return And, return Or]

instance Arbitrary a => Arbitrary (Expression a) where
    arbitrary = sized expro


expro :: Arbitrary a => Int -> Gen (Expression a)
expro 0 = liftM Leaf arbitrary
expro n = oneof [liftM2 UnaryExpr arbitrary (subexpro n),
                 liftM3 BinaryExpr arbitrary (subexpro n) (subexpro n)]

subexpro :: Arbitrary a => Int -> Gen (Expression a)
subexpro n = expro (n `div` 2)

instance Arbitrary Variable where
    arbitrary = liftM Var $ choose ('\97', '\101')

type Mapping = Map.Map Variable Bool
type VarExpr = Expression Variable

------------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------------

oppositeBinary :: BinaryOp -> BinaryOp
oppositeBinary And = Or
oppositeBinary Or = And

equivalent :: VarExpr -> VarExpr -> Bool
equivalent a b = equivalentVars a b && equivalentTruth a b

equivalentVars :: VarExpr -> VarExpr -> Bool
equivalentVars a b = variables a == variables b

equivalentTruth :: VarExpr -> VarExpr -> Bool
equivalentTruth a b = let maps = mappings a
                      in solveWithMappings a maps == solveWithMappings b maps

------------------------------------------------------------------------------
-- Truth table
------------------------------------------------------------------------------

truthTable :: VarExpr -> [Bool]
truthTable expr = map (solveWithMapping expr) $ mappings expr

solveWithMapping :: VarExpr -> Mapping -> Bool
solveWithMapping expr mapping = solve (replace expr mapping)

solveWithMappings :: VarExpr -> [Mapping] -> [Bool]
solveWithMappings expr = map (solveWithMapping expr)

replace :: VarExpr -> Mapping -> Expression Bool
replace (Leaf v) m = Leaf (Map.findWithDefault True v m)
replace (UnaryExpr op expr) m = UnaryExpr op (replace expr m)
replace (BinaryExpr op expr1 expr2) m = BinaryExpr op (replace expr1 m) (replace expr2 m)

mappings :: VarExpr -> [Mapping]
mappings expr = let vs = Set.toList $ variables expr
                    tfs = replicateM (length vs) [True, False]
                in map (Map.fromList . zip vs) tfs

variables :: VarExpr -> Set.Set Variable
variables = foldMap Set.singleton

------------------------------------------------------------------------------
-- Normal Forms
------------------------------------------------------------------------------

-- Negation Normal Form

isNNF :: Expression a -> Bool
isNNF (Leaf _) = True
isNNF (UnaryExpr Not (Leaf _))          = True
isNNF (UnaryExpr Not _)                 = False
isNNF (BinaryExpr _ expr1 expr2)        = isNNF expr1 && isNNF expr2

nnf :: Expression a -> Expression a
nnf = until isNNF (deMorgan . removeDoubleNegation)

removeDoubleNegation :: Expression a -> Expression a
removeDoubleNegation l@(Leaf _) = l
removeDoubleNegation (UnaryExpr Not (UnaryExpr Not expr)) = removeDoubleNegation expr
removeDoubleNegation (UnaryExpr op expr) = UnaryExpr op (removeDoubleNegation expr)
removeDoubleNegation (BinaryExpr op expr1 expr2) = BinaryExpr op (removeDoubleNegation expr1) (removeDoubleNegation expr2)

deMorgan :: Expression a -> Expression a
deMorgan l@(Leaf _) = l
deMorgan (UnaryExpr Not (BinaryExpr op expr1 expr2)) = BinaryExpr (oppositeBinary op) (deMorgan (UnaryExpr Not expr1)) (deMorgan (UnaryExpr Not expr2))
deMorgan (UnaryExpr Not expr) = UnaryExpr Not (deMorgan expr)
deMorgan (BinaryExpr op expr1 expr2) = BinaryExpr op (deMorgan expr1) (deMorgan expr2)

-- Conjunctive Normal Form

isCNF :: Expression a -> Bool
isCNF (Leaf _) = True
isCNF (UnaryExpr Not (Leaf _))          = True
isCNF (UnaryExpr Not _)                 = False
isCNF (BinaryExpr Or expr1 expr2) = isCNF' expr1 expr2
isCNF (BinaryExpr Or (Leaf _) (Leaf _)) = True
isCNF (BinaryExpr Or _ _)               = False
isCNF (BinaryExpr And expr1 expr2)      = isCNF expr1 && isCNF expr2

isCNF' :: Expression a -> Expression a -> Bool
isCNF' expr1 expr2 = case expr1 of
                        (Leaf _) -> isNotOrLeaf expr2
                        (UnaryExpr Not _) -> isNotOrLeaf expr2
                        _ -> False

isNotOrLeaf :: Expression a -> Bool
isNotOrLeaf (Leaf _)          = True
isNotOrLeaf (UnaryExpr Not _) = True
isNotOrLeaf _                 = False


cnf :: Expression a -> Expression a
cnf = until isCNF distributeDisjunction . nnf

distributeDisjunction :: Expression a -> Expression a
distributeDisjunction t@(Leaf _)                            = t
distributeDisjunction t@(UnaryExpr _ _)                     = t
distributeDisjunction t@(BinaryExpr Or (Leaf _) (Leaf _))   = t
distributeDisjunction t@(BinaryExpr Or exprToDistr (BinaryExpr And expr1 expr2)) 
    = distributeDisjunction' exprToDistr expr1 expr2
distributeDisjunction t@(BinaryExpr Or (BinaryExpr And expr1 expr2) exprToDistr) 
    = distributeDisjunction' exprToDistr expr1 expr2
distributeDisjunction t@(BinaryExpr op expr1 expr2)
    = BinaryExpr op (distributeDisjunction expr1) (distributeDisjunction expr2)

distributeDisjunction' :: Expression a -> Expression a -> Expression a -> Expression a
distributeDisjunction' exprToDistr expr1 expr2
    = if isNotOrLeaf exprToDistr
      then BinaryExpr And (BinaryExpr Or exprToDistr expr1) (BinaryExpr Or exprToDistr expr2)
      else BinaryExpr And left right
        where left  = distributeDisjunction (BinaryExpr Or exprToDistr expr1)
              right = distributeDisjunction (BinaryExpr Or exprToDistr expr2)



------------------------------------------------------------------------------
-- Interpreter
------------------------------------------------------------------------------

operateBinary :: BinaryOp -> Bool -> Bool -> Bool
operateBinary And = (&&)
operateBinary Or = (||)

operateUnary :: UnaryOp -> Bool -> Bool
operateUnary Not = not

solve :: Expression Bool -> Bool
solve (Leaf b) = b
solve (UnaryExpr operation  a) = operateUnary operation (solve a)
solve (BinaryExpr operation a b) = operateBinary operation (solve a) (solve b)

------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

ex1 :: VarExpr
ex1 = BinaryExpr Or (Leaf (Var 'A')) (UnaryExpr Not (Leaf (Var 'B')))

ex2 :: VarExpr
ex2 = BinaryExpr And (Leaf (Var 'A')) (Leaf (Var 'B'))

ex3 :: VarExpr
ex3 = BinaryExpr And ex1 ex2

ex :: VarExpr
ex = UnaryExpr Not ex3

main :: IO ()
main = print $ truthTable ex
