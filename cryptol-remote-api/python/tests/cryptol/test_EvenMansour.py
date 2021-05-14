import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.cryptoltypes import CryptolApplication, CryptolLiteral
from cryptol.bitvector import BV


class TestEvenMansour(unittest.TestCase):
    def test_EvenMansour(self):
        c = cryptol.connect()
        c.load_file(str(Path('tests','cryptol','test-files','examples','contrib','EvenMansour.cry')))

        F_10_4 = c.eval('F:[10][4]').result()
        self.assertTrue(c.call('is_a_permutation', F_10_4).result())

        Finv_10_4 = c.eval("F':[10][4]").result()
        digits = [ BV(size=4, value=i) for i in range(0,10) ]
                 # ^ the same as: c.eval('[0..9]:[_][4]').result()
        self.assertTrue(c.call('is_inverse_permutation', digits, F_10_4, Finv_10_4).result())

        self.assertTrue(c.check('E_and_D_are_inverses').result().success)


if __name__ == "__main__":
    unittest.main()
