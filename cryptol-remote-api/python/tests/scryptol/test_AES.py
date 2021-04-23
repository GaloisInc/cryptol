import unittest
from pathlib import Path
import unittest
from cryptol.scryptol import *
from cryptol.bitvector import BV


class TestAES(unittest.TestCase):
    def test_AES(self):
        connect(reset_server=True)
        load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry')))

        pt = BV(size=128, value=0x3243f6a8885a308d313198a2e0370734)
        key = BV(size=128, value=0x2b7e151628aed2a6abf7158809cf4f3c)
        ct = call("aesEncrypt", (pt, key))
        expected_ct = BV(size=128, value=0x3925841d02dc09fbdc118597196a0b32)
        self.assertEqual(ct, expected_ct)

        decrypted_ct = call("aesDecrypt", (ct, key))
        self.assertEqual(pt, decrypted_ct)

        pt = BV(size=128, value=0x00112233445566778899aabbccddeeff)
        key = BV(size=128, value=0x000102030405060708090a0b0c0d0e0f)
        ct = call("aesEncrypt", (pt, key))
        expected_ct = BV(size=128, value=0x69c4e0d86a7b0430d8cdb78070b4c55a)
        self.assertEqual(ct, expected_ct)

        decrypted_ct = call("aesDecrypt", (ct, key))
        self.assertEqual(pt, decrypted_ct)

        self.assertTrue(safe("aesEncrypt"))
        self.assertTrue(safe("aesDecrypt"))
        self.assertTrue(check("AESCorrect").success)
        # c.prove("AESCorrect") # probably takes too long for this script...?



if __name__ == "__main__":
    unittest.main()
