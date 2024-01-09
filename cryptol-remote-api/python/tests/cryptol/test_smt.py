import unittest
from pathlib import Path
import unittest
import cryptol
import cryptol.solver as solver
from cryptol.single_connection import *
from cryptol.bitvector import BV


class TestSMT(unittest.TestCase):
    def test_SMT(self):
        connect(verify=False)
        load_module('Cryptol')

        ex_true  = '\(x : [8]) -> x+x == x+x'
        ex_true_safe = safe(ex_true)
        self.assertTrue(ex_true_safe)
        self.assertIsInstance(ex_true_safe, cryptol.Safe)
        ex_true_prove = prove(ex_true)
        self.assertTrue(ex_true_prove)
        self.assertIsInstance(ex_true_prove, cryptol.Qed)
        ex_true_sat = sat(ex_true)
        self.assertTrue(ex_true_sat)
        self.assertIsInstance(ex_true_sat, cryptol.Satisfiable)

        ex_false = '\(x : [8]) -> x+2*x+1 == x'
        ex_false_safe = safe(ex_false)
        self.assertTrue(ex_false_safe)
        self.assertIsInstance(ex_false_safe, cryptol.Safe)
        ex_false_prove = prove(ex_false)
        self.assertFalse(ex_false_prove)
        self.assertIsInstance(ex_false_prove, cryptol.Counterexample)
        self.assertEqual(ex_false_prove.type, "predicate falsified")
        ex_false_sat = sat(ex_false)
        self.assertFalse(ex_false_sat)
        self.assertIsInstance(ex_false_sat, cryptol.Unsatisfiable)

        ex_partial = '\(x : [8]) -> if x < 0x0f then x == x else error "!"'
        ex_partial_safe = safe(ex_partial)
        self.assertFalse(ex_partial_safe)
        self.assertIsInstance(ex_partial_safe, cryptol.Counterexample)
        self.assertEqual(ex_partial_safe.type, "safety violation")
        ex_partial_prove = prove(ex_partial)
        self.assertFalse(ex_partial_prove)
        self.assertIsInstance(ex_partial_prove, cryptol.Counterexample)
        self.assertEqual(ex_partial_prove.type, "safety violation")
        ex_partial_sat = sat(ex_partial)
        self.assertTrue(ex_partial_sat)
        self.assertIsInstance(ex_partial_sat, cryptol.Satisfiable)

    def test_each_online_solver(self):
        # We test each solver that is packaged for use with what4
        # via https://github.com/GaloisInc/what4-solvers - the others
        # are commented out for now.
        ex_true  = '\(x : [128]) -> negate (complement x + 1) == complement (negate x) + 1'
        solvers = \
            [solver.CVC4,
             solver.CVC5,
             solver.YICES,
             solver.Z3,
             solver.BITWUZLA,
             solver.BOOLECTOR,
             #solver.MATHSAT,
             solver.ABC,
             #solver.OFFLINE,
             solver.ANY,
             solver.SBV_CVC4,
             solver.SBV_CVC5,
             solver.SBV_YICES,
             solver.SBV_Z3,
             solver.SBV_BITWUZLA,
             solver.SBV_BOOLECTOR,
             #solver.SBV_MATHSAT,
             solver.SBV_ABC,
             #solver.SBV_OFFLINE,
             solver.SBV_ANY,
             solver.W4_CVC4,
             solver.W4_CVC5,
             solver.W4_YICES,
             solver.W4_Z3,
             solver.W4_BITWUZLA,
             solver.W4_BOOLECTOR,
             #solver.W4_OFFLINE,
             solver.W4_ABC,
             solver.W4_ANY]

        for s in solvers:
            self.assertTrue(prove(ex_true, s))


if __name__ == "__main__":
    unittest.main()
