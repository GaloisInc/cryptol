import unittest
from argo_client.interaction import ArgoException
from pathlib import Path
import unittest
import io
import time
import cryptol
import cryptol.cryptoltypes
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        self.c = cryptol.connect(verify=False)

    def test_extend_search_path(self):
      """Test that extending the search path acts as expected w.r.t. loads."""
      c = self.c

      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar').result()
      ans1 = c.eval("theAnswer").result()
      ans2 = c.eval("id theAnswer").result()
      self.assertEqual(ans1, ans2)

    def test_logging(self):
      c = self.c
      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')

      log_buffer = io.StringIO()
      c.logging(on=True, dest=log_buffer)
      _ = c.eval("theAnswer").result()
      contents = log_buffer.getvalue()

      self.assertEqual(len(contents.strip().splitlines()), 2,
                       msg=f'log contents: {str(contents.strip().splitlines())}')

      _ = c.eval("theAnswer").result()


    def test_check_timeout(self):
        c = self.c
        c.load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry'))).result()

        t1 = time.time()
        with self.assertRaises(ArgoException):
            c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests="all", timeout=1.0).result()
        t2 = time.time()
        self.assertLess(t2 - t1, 2.0)

        t1 = time.time()
        with self.assertRaises(ArgoException):
            c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests="all", timeout=5.0).result()
        t2 = time.time()
        self.assertLess(t2 - t1, 7)

        t1 = time.time()
        c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests=10, timeout=5.0).result()
        t2 = time.time()
        self.assertLess(t2 - t1, 5)

    def test_interrupt(self):
        c = self.c
        c.load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry')))

        c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests="all")
        # ^ .result() intentionally omitted so we don't wait on it's result and we can interrupt
        # it on the next line.
        time.sleep(.5)
        c.interrupt()
        self.assertTrue(c.safe("aesEncrypt").result())

    def test_prove_timeout(self):
        c = self.c
        c.load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry')))

        pt = BV(size=128, value=0x3243f6a8885a308d313198a2e0370734)
        key = BV(size=128, value=0x2b7e151628aed2a6abf7158809cf4f3c)
        ct = c.call("aesEncrypt", (pt, key)).result()
        expected_ct = BV(size=128, value=0x3925841d02dc09fbdc118597196a0b32)
        self.assertEqual(ct, expected_ct)

        decrypted_ct = c.call("aesDecrypt", (ct, key)).result()
        self.assertEqual(pt, decrypted_ct)

        pt = BV(size=128, value=0x00112233445566778899aabbccddeeff)
        key = BV(size=128, value=0x000102030405060708090a0b0c0d0e0f)
        ct = c.call("aesEncrypt", (pt, key)).result()
        expected_ct = BV(size=128, value=0x69c4e0d86a7b0430d8cdb78070b4c55a)
        self.assertEqual(ct, expected_ct)

        decrypted_ct = c.call("aesDecrypt", (ct, key)).result()
        self.assertEqual(pt, decrypted_ct)

        self.assertTrue(c.safe("aesEncrypt").result())
        self.assertTrue(c.safe("aesDecrypt").result())
        self.assertTrue(c.check("AESCorrect").result().success)
        t1 = time.time()
        with self.assertRaises(ArgoException):
            c.prove("AESCorrect", timeout=1.0).result()
        t2 = time.time()
        # check the timeout worked
        self.assertGreaterEqual(t2 - t1, 1.0)
        self.assertLess(t2 - t1, 5.0)

        # make sure things are still working
        self.assertTrue(c.safe("aesEncrypt").result())

        # set the timeout at the connection level
        c.timeout = 1.0
        t1 = time.time()
        with self.assertRaises(ArgoException):
            c.prove("AESCorrect").result()
        t2 = time.time()
        # check the timeout worked
        self.assertGreaterEqual(t2 - t1, 1.0)
        self.assertLess(t2 - t1, 5.0)

        # make sure things are still working
        c.timeout = None
        self.assertTrue(c.safe("aesEncrypt").result())

        c.timeout = 1.0
        t1 = time.time()
        with self.assertRaises(ArgoException):
            # override timeout with longer time
            c.prove("AESCorrect", timeout=5.0).result()
        t2 = time.time()
        self.assertGreaterEqual(t2 - t1, 5.0)
        self.assertLess(t2 - t1, 10.0)

        # make sure things are still working
        c.timeout = None
        self.assertTrue(c.safe("aesEncrypt").result())


class BasicLoggingServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None
    log_buffer = None

    @classmethod
    def setUpClass(self):
        self.log_buffer = io.StringIO()
        self.c = cryptol.sync.connect(verify=False, log_dest = self.log_buffer)

    @classmethod
    def tearDownClass(self):
        if self.c:
            self.c.reset()

    def test_logging(self):
      c = self.c
      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')
      _ = c.eval("theAnswer")

      self.assertEqual(len(self.log_buffer.getvalue().splitlines()), 6,
                       msg=f'log contents: {str(self.log_buffer.strip().splitlines())}')

if __name__ == "__main__":
    unittest.main()
