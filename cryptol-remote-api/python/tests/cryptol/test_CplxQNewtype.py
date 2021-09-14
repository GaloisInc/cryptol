import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.bitvector import BV


class TestCplxQ(unittest.TestCase):
    def test_CplxQ(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files', 'CplxQNewtype.cry')))

        forty_two = cry_eval("fortyTwo")
        cplx_forty_two1 = call("embedQ", forty_two)
        cplx_forty_two2 = cry_eval("CplxQ{ real = 42, imag = 0 }")
        cplx_two = cry_eval("cplxTwo")
        cplx_forty = cry_eval("cplxForty")
        cplx_forty_two3 = call("cplxAdd", cplx_two, cplx_forty)
        cplx_forty_two4 = cry_eval("cplxMul (CplxQ{ real = 21, imag = 0 }) (CplxQ{ real = 2, imag = 0 })")
        cplx_forty_two5 = cry_eval("cplxAdd (CplxQ{ real = 41, imag = 0 }) (CplxQ{ real = 1, imag = 0 })")
        cplx_forty_two6 = cry_eval("CplxQ{ real = 42, imag = 0 }")

        self.assertTrue(call("cplxEq", cplx_forty_two1, cplx_forty_two2))
        self.assertFalse(call("cplxEq", cplx_two, cplx_forty_two2))
        self.assertTrue(call("cplxEq", cplx_forty_two1, cplx_forty_two3))
        self.assertTrue(call("cplxEq", cplx_forty_two1, cplx_forty_two4))
        self.assertTrue(call("cplxEq", cplx_forty_two1, cplx_forty_two5))
        self.assertTrue(call("cplxEq", cplx_forty_two1, cplx_forty_two6))



if __name__ == "__main__":
    unittest.main()
