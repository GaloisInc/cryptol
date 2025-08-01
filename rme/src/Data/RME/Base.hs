{- |
Module      : Data.RME.Base
Copyright   : Galois, Inc. 2016
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : portable

Reed-Muller Expansion normal form for Boolean Formulas.
-}

module Data.RME.Base
  ( RME
  , true, false, lit
  , constant, isBool
  , compl, xor, conj, disj, iff, mux
  , eval
  , sat, allsat
  , degree
  , depth, size
  , explode
  ) where

-- | Boolean formulas in Algebraic Normal Form, using a representation
-- based on the Reed-Muller expansion.

-- Invariants: The last argument to a `Node` constructor should never
-- be `R0`. Also the `Int` arguments should strictly increase as you
-- go deeper in the tree.

data RME = Node !Int !RME !RME | R0 | R1
  deriving (Eq, Show)

-- | Evaluate formula with given variable assignment.
eval :: RME -> (Int -> Bool) -> Bool
eval anf v =
  case anf of
    R0 -> False
    R1 -> True
    Node n a b -> (eval a v) /= (v n && eval b v)

-- | Normalizing constructor.
node :: Int -> RME -> RME -> RME
node _ a R0 = a
node n a b = Node n a b

-- | Constant true formula.
true :: RME
true = R1

-- | Constant false formula.
false :: RME
false = R0

-- | Boolean constant formulas.
constant :: Bool -> RME
constant False = false
constant True = true

-- | Test whether an RME formula is a constant boolean.
isBool :: RME -> Maybe Bool
isBool R0 = Just False
isBool R1 = Just True
isBool _ = Nothing

-- | Boolean literals.
lit :: Int -> RME
lit n = Node n R0 R1

-- | Logical complement.
compl :: RME -> RME
compl R0 = R1
compl R1 = R0
compl (Node n a b) = Node n (compl a) b

-- | Logical exclusive-or.
xor :: RME -> RME -> RME
xor R0 y = y
xor R1 y = compl y
xor x R0 = x
xor x R1 = compl x
xor x@(Node i a b) y@(Node j c d)
  | i < j = Node i (xor a y) b
  | j < i = Node j (xor x c) d
  | otherwise = node i (xor a c) (xor b d)

-- | Logical conjunction.
conj :: RME -> RME -> RME
conj R0 _ = R0
conj R1 y = y
conj _ R0 = R0
conj x R1 = x
conj x@(Node i a b) y@(Node j c d)
  | i < j = node i (conj a y) (conj b y)
  | j < i = node j (conj x c) (conj x d)
  | otherwise = node i ac (xor ac (conj (xor a b) (xor c d)))
  where ac = conj a c

-- | Logical disjunction.
disj :: RME -> RME -> RME
disj R0 y = y
disj R1 _ = R1
disj x R0 = x
disj _ R1 = R1
disj x@(Node i a b) y@(Node j c d)
  | i < j = node i (disj a y) (conj b (compl y))
  | j < i = node j (disj x c) (conj (compl x) d)
  | otherwise = node i ac (xor ac (disj (xor a b) (xor c d)))
  where ac = disj a c

-- | Logical equivalence.
iff :: RME -> RME -> RME
iff x y = xor (compl x) y
{-
iff R0 y = compl y
iff R1 y = y
iff x R0 = compl x
iff x R1 = x
iff x@(Node i a b) y@(Node j c d)
  | i < j = Node i (iff a y) b
  | j < i = Node j (iff x c) d
  | otherwise = node i (iff a c) (xor b d)
-}

-- | Logical if-then-else.
mux :: RME -> RME -> RME -> RME
--mux w x y = xor (conj w x) (conj (compl w) y)
mux R0 _ y = y
mux R1 x _ = x
mux b x y = xor (conj b (xor x y)) y

{-
mux R0 x y = y
mux R1 x y = x
mux w R0 y = conj (compl w) y
mux w R1 y = disj w y
mux w x R0 = conj w x
mux w x R1 = disj (compl w) x
mux w@(Node i a b) x@(Node j c d) y@(Node k e f)
  | i < j && i < k = node i (mux a x y) (conj b (xor x y))
  | j < i && j < k = node i (mux w c y) (conj w d)
  | k < i && k < j = node i (mux w x e) (conj (compl w) f)
  | i == j && i < k = node i (mux a c y) _
-}

-- | Satisfiability checker.
sat :: RME -> Maybe [(Int, Bool)]
sat R0 = Nothing
sat R1 = Just []
sat (Node n a b) =
  case sat a of
    Just xs -> Just ((n, False) : xs)
    Nothing -> fmap ((n, True) :) (sat b)

-- | List of all satisfying assignments.
allsat :: RME -> [[(Int, Bool)]]
allsat R0 = []
allsat R1 = [[]]
allsat (Node n a b) =
  map ((n, False) :) (allsat a) ++ map ((n, True) :) (allsat (xor a b))

-- | Maximum polynomial degree.
degree :: RME -> Int
degree R0 = 0
degree R1 = 0
degree (Node _ a b) = max (degree a) (1 + degree b)

-- | Tree depth.
depth :: RME -> Int
depth R0 = 0
depth R1 = 0
depth (Node _ a b) = 1 + max (depth a) (depth b)

-- | Tree size.
size :: RME -> Int
size R0 = 1
size R1 = 1
size (Node _ a b) = 1 + size a + size b

-- | Convert to an explicit polynomial representation.
explode :: RME -> [[Int]]
explode R0 = []
explode R1 = [[]]
explode (Node i a b) = explode a ++ map (i:) (explode b)
