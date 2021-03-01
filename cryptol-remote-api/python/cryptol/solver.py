"""Cryptol solver-related definitions"""
from typing import NewType

Solver = NewType('Solver', str)

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
W4_MATHSAT: Solver   = Solver("w4-offline")
W4_ABC: Solver       = Solver("w4-any")
