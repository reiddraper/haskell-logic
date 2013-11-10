{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Control.Applicative (pure, (<$>), (<*>))
import Control.Monad (replicateM, liftM, liftM2, liftM3, mplus)
import Data.Monoid
import Data.Foldable (Foldable, foldMap)
import Data.Data (Data, Typeable)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Lens (Plated(..))
import Control.Lens.Plated (rewrite, universe)

import Test.QuickCheck

------------------------------------------------------------------------------
-- Data declarations
------------------------------------------------------------------------------

data UnaryOp = Not deriving (Eq, Data, Typeable)
data BinaryOp = And | Or deriving (Eq, Data, Typeable)
newtype Variable = Var Char deriving (Eq, Ord, Data, Typeable)

data Expression a
    = Leaf a
    | UnaryExpr UnaryOp (Expression a)
    | BinaryExpr BinaryOp (Expression a) (Expression a)
    deriving (Eq, Data, Typeable)

------------------------------------------------------------------------------
-- Constructor Helpers

-- to cut down on line noise

var :: Char -> VarExpr
var x = Leaf (Var x)

uExprNot :: Expression a -> Expression a
uExprNot = UnaryExpr Not

bExprOr :: Expression a -> Expression a -> Expression a
bExprOr = BinaryExpr Or

bExprAnd :: Expression a -> Expression a -> Expression a
bExprAnd = BinaryExpr And

------------------------------------------------------------------------------
-- Instances

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
    foldMap f (BinaryExpr _ expr1 expr2) = foldMap f expr1 `mappend`
                                           foldMap f expr2

instance Plated (Expression a) where
    plate _ (Leaf l)                    = pure $ Leaf l
    plate f (UnaryExpr op expr)         = UnaryExpr op <$> f expr
    plate f (BinaryExpr op expr1 expr2) = BinaryExpr op <$> f expr1 <*> f expr2

instance Arbitrary UnaryOp where
    arbitrary = return Not
    shrink _  = []

instance Arbitrary BinaryOp where
    arbitrary = oneof [return Or, return And]

    shrink Or = []
    shrink And = [Or]

instance Arbitrary a => Arbitrary (Expression a) where
    arbitrary = sized expro

    shrink (Leaf a)             = map Leaf $ shrink a
    shrink (UnaryExpr op a)     = [UnaryExpr op a' | a' <- shrink a] ++
                                  [UnaryExpr op' a' | op' <- shrink op
                                                    , a' <- a:shrink a]
    shrink (BinaryExpr op a b)  = [BinaryExpr op a' b' | a'  <- shrink a
                                                       , b'  <- shrink b] ++
                                  [BinaryExpr op' a' b' | op' <- shrink op
                                                        , a' <- a:shrink a
                                                        , b' <- b:shrink b]


expro :: Arbitrary a => Int -> Gen (Expression a)
expro 0 = liftM Leaf arbitrary
expro n = oneof [liftM2 UnaryExpr arbitrary (subexpro n),
                 liftM3 BinaryExpr arbitrary (subexpro n) (subexpro n)]

subexpro :: Arbitrary a => Int -> Gen (Expression a)
subexpro n = expro (n `div` 2)

-- Really a `[Char]`, but String syntax is easier on the
-- eyes.
variableLetters :: String
variableLetters = "abcde"

instance Arbitrary Variable where
    arbitrary = liftM Var $ elements variableLetters

    shrink (Var 'a') = map Var []
    shrink (Var 'b') = map Var "a"
    shrink (Var 'c') = map Var "ab"
    shrink (Var 'd') = map Var "abc"
    shrink (Var 'e') = map Var "abcd"
    shrink _         = []

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
solveWithMapping = (solve .) . replace

solveWithMappings :: VarExpr -> [Mapping] -> [Bool]
solveWithMappings = map . solveWithMapping

replace :: VarExpr -> Mapping -> Expression Bool
replace (Leaf v) m = Leaf (Map.findWithDefault True v m)
replace (UnaryExpr op expr) m = UnaryExpr op (replace expr m)
replace (BinaryExpr op expr1 expr2) m = BinaryExpr op (replace expr1 m)
                                                      (replace expr2 m)

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

isNNF :: (Data a, Typeable a) => Expression a -> Bool
isNNF = all doubleNegation . universe
    where doubleNegation (UnaryExpr Not (Leaf _))   = True
          doubleNegation (UnaryExpr Not _)          = False
          doubleNegation _                          = True

nnf :: (Data a, Typeable a) => Expression a -> Expression a
nnf = rewrite (\e -> deMorgan e `mplus` removeDoubleNegation e)

removeDoubleNegation :: (Typeable a, Data a) => Expression a -> Maybe (Expression a)
removeDoubleNegation (UnaryExpr Not (UnaryExpr Not a)) = Just a
removeDoubleNegation _ = Nothing

deMorgan :: (Data a, Typeable a) => Expression a -> Maybe (Expression a)
deMorgan (UnaryExpr Not (BinaryExpr op a b)) = Just $ BinaryExpr (oppositeBinary op) (uExprNot a) (uExprNot b)
deMorgan _ = Nothing

-- Conjunctive Normal Form

isCNF :: (Data a, Typeable a) => Expression a -> Bool
isCNF = all cnf' . universe
    where cnf' (UnaryExpr Not (Leaf _)) = True
          cnf' (UnaryExpr Not _)        = False
          cnf' (BinaryExpr Or a b)      = isNotAnd a && isNotAnd b
          cnf' _                        = True

isNotAnd :: (Data a, Typeable a) => Expression a -> Bool
isNotAnd a = null [() | BinaryExpr And _ _ <- universe a]

cnf :: (Data a, Typeable a) => Expression a -> Expression a
cnf = rewrite distributeDisjunction . nnf

distributeDisjunction :: (Data a, Typeable a) => Expression a -> Maybe (Expression a)
distributeDisjunction (BinaryExpr Or exprToDistr (BinaryExpr And expr1 expr2))
    = distributeDisjunction' exprToDistr expr1 expr2
distributeDisjunction (BinaryExpr Or (BinaryExpr And expr1 expr2) exprToDistr)
    = distributeDisjunction' exprToDistr expr1 expr2
distributeDisjunction _ = Nothing

distributeDisjunction' :: (Data a, Typeable a) => Expression a -> Expression a -> Expression a -> Maybe (Expression a)
distributeDisjunction' exprToDistr expr1 expr2
    = Just $ bExprAnd (bExprOr expr1 exprToDistr) (bExprOr expr2 exprToDistr)

-- Disjunctive Normal Form

isDNF :: (Data a, Typeable a) => Expression a -> Bool
isDNF = all dnf' . universe
    where dnf' (UnaryExpr Not (Leaf _)) = True
          dnf' (UnaryExpr Not _)        = False
          dnf' (BinaryExpr And a b)     = isNotOr a && isNotOr b
          dnf' _                        = True

isNotOr :: (Data a, Typeable a) => Expression a -> Bool
isNotOr a = null [() | BinaryExpr Or _ _ <- universe a]

dnf :: (Data a, Typeable a) => Expression a -> Expression a
dnf = rewrite distributeConjunction . nnf

distributeConjunction :: (Data a, Typeable a) => Expression a -> Maybe (Expression a)
distributeConjunction (BinaryExpr And exprToDistr (BinaryExpr Or expr1 expr2))
    = distributeConjunction' exprToDistr expr1 expr2
distributeConjunction (BinaryExpr And (BinaryExpr Or expr1 expr2) exprToDistr)
    = distributeConjunction' exprToDistr expr1 expr2
distributeConjunction _ = Nothing

distributeConjunction' :: (Data a, Typeable a) => Expression a -> Expression a -> Expression a -> Maybe (Expression a)
distributeConjunction' exprToDistr expr1 expr2
    = Just $ bExprOr (bExprAnd expr1 exprToDistr) (bExprAnd expr2 exprToDistr)

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
-- QC Properties
------------------------------------------------------------------------------

type ExprProp = VarExpr -> Bool

-- equivalence

propNNFEquiv :: ExprProp
propNNFEquiv e = equivalent e (nnf e)

propCNFEquiv :: ExprProp
propCNFEquiv e = equivalent e (cnf e)

propDNFEquiv :: ExprProp
propDNFEquiv e = equivalent e (dnf e)

-- correctness

propNNFisNNF :: ExprProp
propNNFisNNF e = isNNF (nnf e)

propCNFIsNNF :: ExprProp
propCNFIsNNF e = isNNF (cnf e)

propDNFIsNNF :: ExprProp
propDNFIsNNF e = isNNF (dnf e)

propCNFisCNF :: ExprProp
propCNFisCNF e = isCNF (cnf e)

propDNFisDNF :: ExprProp
propDNFisDNF e = isDNF (dnf e)

-- idempotency

propNNFIdempotent :: ExprProp
propNNFIdempotent e = (nnf . nnf) e == nnf e

propCNFIdempotent :: ExprProp
propCNFIdempotent e = (cnf . cnf) e == cnf e

propDNFIdempotent :: ExprProp
propDNFIdempotent e = (dnf . dnf) e == dnf e

-- Running helpers

ar ::  Args
ar = stdArgs {maxSuccess = 512}

propWithAr ::  (Expression Variable -> Bool) -> IO ()
propWithAr = quickCheckWith ar

props :: [IO ()]
props = map propWithAr [propNNFEquiv,
                        propCNFEquiv,
                        propDNFEquiv,
                        propCNFIsNNF,
                        propDNFIsNNF,
                        propNNFisNNF,
                        propCNFisCNF,
                        propDNFisDNF,
                        propNNFIdempotent,
                        propCNFIdempotent]

runProps :: IO ()
runProps = sequence_ props

------------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------------

ex1 :: VarExpr
ex1 = bExprAnd (var 'A') (uExprNot (var 'B'))

ex2 :: VarExpr
ex2 = bExprAnd (var 'A') (var 'B')

ex3 :: VarExpr
ex3 = bExprAnd ex1 ex2

ex :: VarExpr
ex = uExprNot ex3

main :: IO ()
main = runProps
