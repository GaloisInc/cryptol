import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.bitvector import BV


class TestDES(unittest.TestCase):
    def test_DES(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','examples','DEStest.cry')))

        # we can run the test suite as indended...
        # vkres = cry_eval('vktest DES')
        # self.assertTrue(all(passed for (_,_,passed) in vkres))
        # vtres = cry_eval('vttest DES')
        # self.assertTrue(all(passed for (_,_,passed) in vtres))
        # kares = cry_eval('katest DES')
        # self.assertTrue(all(passed for (_,_,passed) in kares))

        # ...but we can also do it manually, using the python bindings more
        def test(key, pt0, ct0):
            ct1 = call('DES.encrypt', key, pt0)
            pt1 = call('DES.decrypt', key, ct0)
            self.assertEqual(ct0, ct1)
            self.assertEqual(pt0, pt1)

        # vktest
        vk = cry_eval('vk')
        pt0 = BV(size=64, value=0)
        for (key, ct0) in vk:
            test(key, pt0, ct0)

        # vttest
        vt = cry_eval('vt')
        key = BV(size=64, value=0x0101010101010101)
        for (pt0, ct0) in vt:
            test(key, pt0, ct0)

        # katest
        ka = cry_eval('ka')
        for (key, pt0, ct0) in ka:
            test(key, pt0, ct0)


if __name__ == "__main__":
    unittest.main()
