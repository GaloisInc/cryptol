"""Cryptol solver-related definitions"""
from typing import NewType

from dataclasses import dataclass

@dataclass
class OfflineSmtQuery():
  """An SMTLIB2 script -- produced when an `offline` prover is used."""
  content: str

class Solver():
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

  def without_hash_consing(self) -> 'Solver':
    """Returns an identical solver but with hash consing disabled (if applicable)."""
    return Solver(name=self.__name, hash_consing=False)

# Cryptol-supported SMT configurations/solvers
# (see Cryptol.Symbolic.SBV Haskell module)
CVC4: Solver          = Solver("cvc4")
YICES: Solver         = Solver("yices")
Z3: Solver            = Solver("z3")
BOOLECTOR: Solver     = Solver("boolector")
MATHSAT: Solver       = Solver("mathsat")
ABC: Solver           = Solver("abc")
OFFLINE: Solver       = Solver("offline")
ANY: Solver           = Solver("any")
SBV_CVC4: Solver      = Solver("sbv-cvc4")
SBV_YICES: Solver     = Solver("sbv-yices")
SBV_Z3: Solver        = Solver("sbv-z3")
SBV_BOOLECTOR: Solver = Solver("sbv-boolector")
SBV_MATHSAT: Solver   = Solver("sbv-mathsat")
SBV_ABC: Solver       = Solver("sbv-abc")
SBV_OFFLINE: Solver   = Solver("sbv-offline")
SBV_ANY: Solver       = Solver("sbv-any")
W4_CVC4: Solver      = Solver("w4-cvc4")
W4_YICES: Solver     = Solver("w4-yices")
W4_Z3: Solver        = Solver("w4-z3")
W4_BOOLECTOR: Solver = Solver("w4-boolector")
W4_OFFLINE: Solver   = Solver("w4-offline")
W4_ABC: Solver       = Solver("w4-any")
