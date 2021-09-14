import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.bitvector import BV


class TestEvenMansour(unittest.TestCase):
    def test_EvenMansour(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','examples','contrib','EvenMansour.cry')))

        F_10_4 = cry_eval('F:[10][4]')
        self.assertTrue(call('is_a_permutation', F_10_4))

        Finv_10_4 = cry_eval("F':[10][4]")
        digits = [ BV(size=4, value=i) for i in range(0,10) ]
                 # ^ the same as: c.eval('[0..9]:[_][4]')
        self.assertTrue(call('is_inverse_permutation', digits, F_10_4, Finv_10_4))

        self.assertTrue(check('E_and_D_are_inverses'))


if __name__ == "__main__":
    unittest.main()
