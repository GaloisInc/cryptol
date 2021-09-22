import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.cryptoltypes import CryptolLiteral
from cryptol.bitvector import BV


class TestSHA256(unittest.TestCase):
    def test_SHA256(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','examples','param_modules','SHA.cry')))

        m1 = CryptolLiteral('"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"')
        j1 = call('join', m1)
        h1 = call('sha256', j1)
        expected_h1 = BV(size=256, value=0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1)
        self.assertEqual(h1, expected_h1)

        m2 = CryptolLiteral('""')
        j2 = call('join', m2)
        h2 = call('sha256', j2)
        expected_h2 = BV(size=256, value=0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855)
        self.assertEqual(h2, expected_h2)

        m3 = CryptolLiteral('"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"')
        j3 = call('join', m3)
        h3 = call('sha256', j3)
        expected_h3 = BV(size=256, value=0xcf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1)
        self.assertEqual(h3, expected_h3)


if __name__ == "__main__":
    unittest.main()
