import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.cryptoltypes import CryptolApplication, CryptolLiteral
from cryptol.bitvector import BV


class TestSHA256(unittest.TestCase):
    def test_SHA256(self):
        c = cryptol.connect()
        c.load_file(str(Path('tests','cryptol','test-files','examples','param_modules','SHA.cry')))

        m1 = CryptolLiteral('"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"')
        j1 = c.call('join', m1).result()
        h1 = c.call('sha256', j1).result()
        expected_h1 = BV(size=256, value=0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1)
        self.assertEqual(h1, expected_h1)

        m2 = CryptolLiteral('""')
        j2 = c.call('join', m2).result()
        h2 = c.call('sha256', j2).result()
        expected_h2 = BV(size=256, value=0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855)
        self.assertEqual(h2, expected_h2)

        m3 = CryptolLiteral('"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"')
        j3 = c.call('join', m3).result()
        h3 = c.call('sha256', j3).result()
        expected_h3 = BV(size=256, value=0xcf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1)
        self.assertEqual(h3, expected_h3)


if __name__ == "__main__":
    unittest.main()
