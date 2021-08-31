import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.bitvector import BV


class TestCplxQ(unittest.TestCase):
    def test_CplxQ(self):
        c = cryptol.connect(verify=False)
        c.load_file(str(Path('tests','cryptol','test-files', 'CplxQNewtype.cry')))

        forty_two = c.eval("fortyTwo").result()
        cplx_forty_two1 = c.call("embedQ", forty_two).result()
        cplx_forty_two2 = c.eval("CplxQ{ real = 42, imag = 0 }").result()
        cplx_two = c.eval("cplxTwo").result()
        cplx_forty = c.eval("cplxForty").result()
        cplx_forty_two3 = c.call("cplxAdd", cplx_two, cplx_forty).result()
        cplx_forty_two4 = c.eval("cplxMul (CplxQ{ real = 21, imag = 0 }) (CplxQ{ real = 2, imag = 0 })").result()
        cplx_forty_two5 = c.eval("cplxAdd (CplxQ{ real = 41, imag = 0 }) (CplxQ{ real = 1, imag = 0 })").result()
        cplx_forty_two6 = c.eval("CplxQ{ real = 42, imag = 0 }").result()

        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two2).result())
        self.assertFalse(c.call("cplxEq", cplx_two, cplx_forty_two2).result())
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two3).result())
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two4).result())
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two5).result())
        self.assertTrue(c.call("cplxEq", cplx_forty_two1, cplx_forty_two6).result())



if __name__ == "__main__":
    unittest.main()
