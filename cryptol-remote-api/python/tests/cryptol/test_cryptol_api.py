import unittest
from pathlib import Path
import os
from pathlib import Path
import subprocess
import time
import unittest
import signal
from distutils.spawn import find_executable
import cryptol
import argo_client.connection as argo
import cryptol.cryptoltypes
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import * #type: ignore


class CryptolTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        self.c = cryptol.connect()
        self.c.load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))

    @classmethod
    def tearDownClass(self):
        if self.c:
            self.c.reset()

    def test_low_level(self):
        c = self.c
        x_val = c.evaluate_expression("x").result()

        self.assertEqual(c.eval("Id::id x").result(), x_val)
        self.assertEqual(c.call('Id::id', bytes.fromhex('ff')).result(), BV(8,255))

        self.assertEqual(c.call('add', b'\0', b'\1').result(), BV(8,1))
        self.assertEqual(c.call('add', bytes.fromhex('ff'), bytes.fromhex('03')).result(), BV(8,2))

    # AMK: importing cryptol bindings into Python temporarily broken due to linear state usage changes
    # in argo approx 1 March 2020
    # def test_module_import(self):
    #     c = self.c
    #     cryptol.add_cryptol_module('Foo', c)
    #     from Foo import add
    #     self.assertEqual(add(b'\2', 2), BV(8,4))

    #     self.assertEqual(add(BitVector( intVal = 0, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,1))
    #     self.assertEqual(add(BitVector( intVal = 1, size = 8 ), BitVector( intVal = 2, size = 8 )), BV(8,3))
    #     self.assertEqual(add(BitVector( intVal = 255, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,0))
    #     self.assertEqual(add(BV(8,0),   BV(8,1)), BV(8,1))
    #     self.assertEqual(add(BV(8,1),   BV(8,2)), BV(8,3))
    #     self.assertEqual(add(BV(8,255), BV(8,1)), BV(8,0))

    def test_sat(self):
        c = self.c
        # test a single sat model can be returned
        rootsOf9 = c.sat('isSqrtOf9').result()
        self.assertEqual(len(rootsOf9), 1)
        self.assertTrue(int(rootsOf9[0]) ** 2 % 256, 9)

        # check we can specify the solver
        rootsOf9 = c.sat('isSqrtOf9', solver = solver.ANY).result()
        self.assertEqual(len(rootsOf9), 1)
        self.assertTrue(int(rootsOf9[0]) ** 2 % 256, 9)

        # check we can ask for a specific number of results
        rootsOf9 = c.sat('isSqrtOf9', count = 3).result()
        self.assertEqual(len(rootsOf9), 3)
        self.assertEqual([int(root) ** 2 % 256 for root in rootsOf9], [9,9,9])

        # check we can ask for all results
        rootsOf9 = c.sat('isSqrtOf9', count = None).result()
        self.assertEqual(len(rootsOf9), 4)
        self.assertEqual([int(root) ** 2 % 256 for root in rootsOf9], [9,9,9,9])

        # check for an unsat condition
        self.assertFalse(c.sat('\\x -> isSqrtOf9 x && ~(elem x [3,131,125,253])').result())

        # check for a valid condition
        self.assertTrue(c.prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]').result())

    def test_check(self):
        c = self.c
        res = c.check("\\x -> x==(x:[8])").result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 100)
        self.assertEqual(res.tests_possible, 256)
        self.assertFalse(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> x==(x:[8])", num_tests=1).result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 1)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> x==(x:[8])", num_tests=42).result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 42)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> x==(x:[8])", num_tests=1000).result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 256)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> x==(x:[8])", num_tests='all').result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 256)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> x==(x:Integer)", num_tests=1024).result()
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 1024)
        self.assertEqual(res.tests_possible, None)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> (x + 1)==(x:[8])").result()
        self.assertFalse(res.success)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 1)
        self.assertEqual(res.error_msg, None)

        res = c.check("\\x -> (x / 0)==(x:[8])").result()
        self.assertFalse(res.success)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 1)
        self.assertIsInstance(res.error_msg, str)

    def test_safe(self):
        c = self.c
        res = c.safe("\\x -> x==(x:[8])").result()
        self.assertTrue(res)

        res = c.safe("\\x -> x / (x:[8])").result()
        self.assertEqual(res, [BV(size=8, value=0)])


    def test_many_usages_one_connection(self):
        c = self.c
        for i in range(0,100):
            x_val1 = c.evaluate_expression("x").result()
            x_val2 = c.eval("Id::id x").result()
            self.assertEqual(x_val1, x_val2)



class HttpMultiConnectionTests(unittest.TestCase):
    # Connection to server
    c = None
    # Python initiated process running the server (if any)
    p = None
    # url of HTTP server
    url = None

    @classmethod
    def setUpClass(self):
        server = os.getenv('CRYPTOL_SERVER_URL')
        if server is not None:
            self.url = server
        else:
            server = os.getenv('CRYPTOL_SERVER')
            if server is not None:
                server = find_executable(server)
            if server is None:
                server = find_executable('cryptol-remote-api')
            if server is not None:
                self.p = subprocess.Popen(
                    [server, "http", "/", "--port", "8080"],
                    stdout=subprocess.PIPE,
                    stdin=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                    start_new_session=True)
                time.sleep(5)
                assert(self.p is not None)
                poll_result = self.p.poll()
                if poll_result is not None:
                    print(poll_result)
                    print(self.p.stdout.read())
                    print(self.p.stderr.read())
                assert(poll_result is None)
                self.url = "http://localhost:8080/"
            else:
                raise RuntimeError("NO CRYPTOL SERVER FOUND")

    @classmethod
    def tearDownClass(self):
        if self.p is not None:
            os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
        super().tearDownClass()

    def test_reset_with_many_usages_many_connections(self):
        for i in range(0,100):
            time.sleep(.05)
            c = cryptol.connect(url=self.url)
            c.load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))
            x_val1 = c.evaluate_expression("x").result()
            x_val2 = c.eval("Id::id x").result()
            self.assertEqual(x_val1, x_val2)
            c.reset()

    def test_reset_server_with_many_usages_many_connections(self):
        for i in range(0,100):
            time.sleep(.05)
            c = cryptol.connect(url=self.url, reset_server=True)
            c.load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))
            x_val1 = c.evaluate_expression("x").result()
            x_val2 = c.eval("Id::id x").result()
            self.assertEqual(x_val1, x_val2)


if __name__ == "__main__":
    unittest.main()
