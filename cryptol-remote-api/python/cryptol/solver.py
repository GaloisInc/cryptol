"""Cryptol solver-related definitions"""
from abc import ABCMeta, abstractmethod
from typing import Any

from dataclasses import dataclass

@dataclass
class OfflineSmtQuery():
  """An SMTLIB2 script -- produced when an `offline` prover is used. Instances
  of this class are neither truthy nor falsy, using an instance of this class
  in an 'if' or 'while' statement will result in an error.
  """
  content: str

  def __bool__(self) -> Any:
    raise ValueError("Offline SMT query has no value")
  def __nonzero__(self) -> Any:
    raise ValueError("Offline SMT query has no value")

class Solver(metaclass=ABCMeta):
  """An SMT solver mode selectable for Cryptol. Compare with the `:set prover` options in
  the Cryptol REPL."""
  __name: str
  __hash_consing: bool

  def __init__(self, name:str, hash_consing:bool=True) -> None:
    self.__name = name
    self.__hash_consing = hash_consing

  def name(self) -> str:
    """Returns a string describing the solver setup which Cryptol will recognize -- i.e.,
    see the options available via `:set prover = NAME`."""
    return self.__name

  def hash_consing(self) -> bool:
    """Returns whether hash consing is enabled (if applicable)."""
    return self.__hash_consing

  @abstractmethod
  def without_hash_consing(self) -> 'Solver':
    """Returns an identical solver but with hash consing disabled (if applicable)."""
    pass

class OnlineSolver(Solver):
  def without_hash_consing(self) -> 'OnlineSolver':
    return OnlineSolver(name=self.name(), hash_consing=False)

class OfflineSolver(Solver):
  def without_hash_consing(self) -> 'OfflineSolver':
    return OfflineSolver(name=self.name(), hash_consing=False)

# Cryptol-supported SMT configurations/solvers
# (see Cryptol.Symbolic.SBV Haskell module)
CVC4: OnlineSolver          = OnlineSolver("cvc4")
CVC5: OnlineSolver          = OnlineSolver("cvc5")
YICES: OnlineSolver         = OnlineSolver("yices")
Z3: OnlineSolver            = OnlineSolver("z3")
BOOLECTOR: OnlineSolver     = OnlineSolver("boolector")
MATHSAT: OnlineSolver       = OnlineSolver("mathsat")
ABC: OnlineSolver           = OnlineSolver("abc")
OFFLINE: OfflineSolver      = OfflineSolver("offline")
ANY: OnlineSolver           = OnlineSolver("any")
SBV_CVC4: OnlineSolver      = OnlineSolver("sbv-cvc4")
SBV_CVC5: OnlineSolver      = OnlineSolver("sbv-cvc5")
SBV_YICES: OnlineSolver     = OnlineSolver("sbv-yices")
SBV_Z3: OnlineSolver        = OnlineSolver("sbv-z3")
SBV_BOOLECTOR: OnlineSolver = OnlineSolver("sbv-boolector")
SBV_MATHSAT: OnlineSolver   = OnlineSolver("sbv-mathsat")
SBV_ABC: OnlineSolver       = OnlineSolver("sbv-abc")
SBV_OFFLINE: OfflineSolver  = OfflineSolver("sbv-offline")
SBV_ANY: OnlineSolver       = OnlineSolver("sbv-any")
W4_CVC4: OnlineSolver       = OnlineSolver("w4-cvc4")
W4_CVC5: OnlineSolver       = OnlineSolver("w4-cvc5")
W4_YICES: OnlineSolver      = OnlineSolver("w4-yices")
W4_Z3: OnlineSolver         = OnlineSolver("w4-z3")
W4_BOOLECTOR: OnlineSolver  = OnlineSolver("w4-boolector")
W4_OFFLINE: OfflineSolver   = OfflineSolver("w4-offline")
W4_ABC: OnlineSolver        = OnlineSolver("w4-abc")
W4_ANY: OnlineSolver        = OnlineSolver("w4-any")
