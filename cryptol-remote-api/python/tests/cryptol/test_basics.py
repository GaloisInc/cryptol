import unittest
from argo_client.interaction import ArgoException
from pathlib import Path
import unittest
import io
import os
import time
from shutil import which
import cryptol
import cryptol.cryptoltypes
from cryptol.single_connection import *
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        self.c = cryptol.connect(verify=False)

    def test_extend_search_path(self):
      # Test that extending the search path acts as expected w.r.t. loads
      c = self.c

      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar').result()
      ans1 = c.eval("theAnswer").result()
      ans2 = c.eval("id theAnswer").result()
      self.assertEqual(ans1, ans2)

    def test_logging(self):
      c = self.c
      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar').result()

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
        # Check if this test is using a local server, if not we assume it's a remote HTTP server
        if os.getenv('CRYPTOL_SERVER') is not None or which('cryptol-remote-api'):
            c = self.c
            c.load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry')))

            t1 = time.time()
            c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests="all", timeout=30.0)
            # ^ .result() intentionally omitted so we don't wait on it's result and we can interrupt
            # it on the next line. We add a timeout just in case to the test fails
            time.sleep(.5)
            c.interrupt()
            self.assertTrue(c.safe("aesEncrypt").result())
            t2 = time.time()
            self.assertLess(t2 - t1, 15.0) # ensure th interrupt ended things and not the timeout
        elif os.getenv('CRYPTOL_SERVER_URL') is not None:
            c = self.c
            other_c = cryptol.connect(verify=False)
            # Since this is the HTTP server, due to client implementation details
            # the requests don't return until they get a response, so we fork
            # to interrupt the server
            newpid = os.fork()
            if newpid == 0:
                time.sleep(5)
                other_c.interrupt()
                os._exit(0)

            c.load_file(str(Path('tests','cryptol','test-files', 'examples','AES.cry')))

            t1 = time.time()
            c.check("\\(bv : [256]) -> ~ (~ (~ (~bv))) == bv", num_tests="all", timeout=60.0)
            self.assertTrue(c.safe("aesEncrypt").result())
            t2 = time.time()
            self.assertLess(t2 - t1, 20.0) # ensure th interrupt ended things and not the timeout
        else:
            # Otherwise fail... since this shouldn't be possible
            self.assertFalse("Impossible")


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
    log_buffer = None

    @classmethod
    def setUpClass(self):
        self.log_buffer = io.StringIO()
        connect(verify=False, log_dest = self.log_buffer)

    def test_logging(self):
      extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      load_module('Bar')
      _ = cry_eval("theAnswer")
      content_lines = self.log_buffer.getvalue().strip().splitlines()

      self.assertEqual(len(content_lines), 6,
                       msg=f'log contents: {str(content_lines)}')

if __name__ == "__main__":
    unittest.main()
