-- See Note [-Wincomplete-uni-patterns and irrefutable patterns]
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.TypePat
  ( aInf, aNat, aNat'

  , anAdd, (|-|), aMul, (|^|), (|/|), (|%|)
  , aMin, aMax
  , aWidth
  , aCeilDiv, aCeilMod
  , aLenFromThenTo

  , aLiteral
  , aLiteralLessThan
  , aLogic
  , aIntegral

  , aTVar
  , aFreeTVar
  , aBit
  , aSeq
  , aWord
  , aChar
  , aTuple
  , aRec
  , (|->|)

  , aFin, aPrime, (|=|), (|/=|), (|>=|)
  , aAnd
  , aTrue

  , anError

  , module Cryptol.Utils.Patterns
  ) where

import Control.Applicative((<|>))
import Control.Monad
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Patterns
import Cryptol.Utils.RecordMap
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.InfNat


tcon :: TCon -> ([Type] -> a) -> Pat Type a
tcon f p = \ty -> case tNoUser ty of
                    TCon c ts | f == c -> return (p ts)
                    _                  -> mzero

ar0 :: [a] -> ()
ar0 ~[] = ()

ar1 :: [a] -> a
ar1 ~[a] = a

ar2 :: [a] -> (a,a)
ar2 ~[a,b] = (a,b)

ar3 :: [a] -> (a,a,a)
ar3 ~[a,b,c] = (a,b,c)

tf :: TFun -> ([Type] -> a) -> Pat Type a
tf f ar = tcon (TF f) ar

tc :: TC -> ([Type] -> a) -> Pat Type a
tc f ar = tcon (TC f) ar

tp :: PC -> ([Type] -> a) -> Pat Prop a
tp f ar = tcon (PC f) ar


--------------------------------------------------------------------------------

aInf :: Pat Type ()
aInf = tc TCInf ar0

aNat :: Pat Type Integer
aNat = \a -> case tNoUser a of
               TCon (TC (TCNum n)) _ -> return n
               _                     -> mzero

aNat' :: Pat Type Nat'
aNat' = \a -> (Inf <$  aInf a)
          <|> (Nat <$> aNat a)

anAdd :: Pat Type (Type,Type)
anAdd = tf TCAdd ar2

(|-|) :: Pat Type (Type,Type)
(|-|) = tf TCSub ar2

aMul :: Pat Type (Type,Type)
aMul = tf TCMul ar2

(|^|) :: Pat Type (Type,Type)
(|^|) = tf TCExp ar2

(|/|) :: Pat Type (Type,Type)
(|/|) = tf TCDiv ar2

(|%|) :: Pat Type (Type,Type)
(|%|) = tf TCMod ar2

aMin :: Pat Type (Type,Type)
aMin = tf TCMin ar2

aMax :: Pat Type (Type,Type)
aMax = tf TCMax ar2

aWidth :: Pat Type Type
aWidth = tf TCWidth ar1

aCeilDiv :: Pat Type (Type,Type)
aCeilDiv = tf TCCeilDiv ar2

aCeilMod :: Pat Type (Type,Type)
aCeilMod = tf TCCeilMod ar2

aLenFromThenTo :: Pat Type (Type,Type,Type)
aLenFromThenTo = tf TCLenFromThenTo ar3

--------------------------------------------------------------------------------
aTVar :: Pat Type TVar
aTVar = \a -> case tNoUser a of
                TVar x -> return x
                _      -> mzero

aFreeTVar :: Pat Type TVar
aFreeTVar t =
  do v <- aTVar t
     guard (isFreeTV v)
     return v

aBit :: Pat Type ()
aBit = tc TCBit ar0

aSeq :: Pat Type (Type,Type)
aSeq = tc TCSeq ar2

aWord :: Pat Type Type
aWord = \a -> do (l,t) <- aSeq a
                 aBit t
                 return l

aChar :: Pat Type ()
aChar = \a -> do (l,t) <- aSeq a
                 n     <- aNat l
                 guard (n == 8)
                 aBit t

aTuple :: Pat Type [Type]
aTuple = \a -> case tNoUser a of
                 TCon (TC (TCTuple _)) ts -> return ts
                 _                        -> mzero

aRec :: Pat Type (RecordMap Ident Type)
aRec = \a -> case tNoUser a of
               TRec fs -> return fs
               _       -> mzero

(|->|) :: Pat Type (Type,Type)
(|->|) = tc TCFun ar2
--------------------------------------------------------------------------------

aFin :: Pat Prop Type
aFin = tp PFin ar1

aPrime :: Pat Prop Type
aPrime = tp PPrime ar1

(|=|) :: Pat Prop (Type,Type)
(|=|) = tp PEqual ar2

(|/=|) :: Pat Prop (Type,Type)
(|/=|) = tp PNeq ar2

(|>=|) :: Pat Prop (Type,Type)
(|>=|) = tp PGeq ar2

aAnd :: Pat Prop (Prop,Prop)
aAnd = tp PAnd ar2

aTrue :: Pat Prop ()
aTrue = tp PTrue ar0

aLiteral :: Pat Prop (Type,Type)
aLiteral = tp PLiteral ar2

aLiteralLessThan :: Pat Prop (Type,Type)
aLiteralLessThan = tp PLiteralLessThan ar2

aLogic :: Pat Prop Type
aLogic = tp PLogic ar1

aIntegral :: Pat Prop Type
aIntegral = tp PIntegral ar1

--------------------------------------------------------------------------------
anError :: Kind -> Pat Type ()
anError k = \a -> case tNoUser a of
                    TCon (TError (_ :-> k1) ) _ | k == k1 -> return ()
                    _                                     -> mzero


{-
Note [-Wincomplete-uni-patterns and irrefutable patterns]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Various parts of Cryptol use irrefutable patterns in functions that assume that
their arguments have particular shapes. For example, the `ar1 ~[a] = a`
function in this module uses an irrefutable pattern because it assumes the
invariant that the argument list will have exactly one element. This lets ar1
be slightly lazier when evaluated.

Unfortunately, this use of irrefutable patterns is at odds with the
-Wincomplete-uni-patterns warning. At present, -Wincomplete-uni-patterns will
produce a warning for any irrefutable pattern that does not cover all possible
data constructors. While we could rewrite functions like `ar1` to explicitly
provide a fall-through case, that would change its strictness properties. As
a result, we simply disable -Wincomplete-uni-patterns warnings in each part
of Cryptol that uses irrefutable patterns.

Arguably, -Wincomplete-uni-patterns shouldn't be producing warnings for
irrefutable patterns at all. GHC issue #14800
(https://gitlab.haskell.org/ghc/ghc/-/issues/14800) proposes this idea.
If that issue is fixed in the future, we may want to reconsider whether we want
to disable -Wincomplete-uni-patterns.
-}
