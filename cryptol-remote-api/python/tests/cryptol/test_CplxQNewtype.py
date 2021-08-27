import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.bitvector import BV


class TestCplxQ(unittest.TestCase):
    def test_CplxQ(self):
        c = cryptol.connect_sync(reset_server=True, verify=False)
        c.load_file(str(Path('tests','cryptol','test-files', 'CplxQNewtype.cry')))

        forty_two = c.eval("fortyTwo")
        cplx_forty_two1 = c.call("embedQ", forty_two)
        cplx_forty_two2 = c.eval("CplxQ{ real = 42, imag = 0 }")
        cplx_two = c.eval("cplxTwo")
        cplx_forty = c.eval("cplxForty")
        cplx_forty_two3 = c.call("cplxAdd", cplx_two, cplx_forty)
        cplx_forty_two4 = c.eval("cplxMul (CplxQ{ real = 21, imag = 0 }) (CplxQ{ real = 2, imag = 0 })")
        cplx_forty_two5 = c.eval("cplxAdd (CplxQ{ real = 41, imag = 0 }) (CplxQ{ real = 1, imag = 0 })")
        cplx_forty_two6 = c.eval("CplxQ{ real = 42, imag = 0 }")

        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two2))
        self.assertFalse(c.call("cplxEq", cplx_two, cplx_forty_two2))
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two3))
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two4))
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two5))
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two6))



if __name__ == "__main__":
    unittest.main()
