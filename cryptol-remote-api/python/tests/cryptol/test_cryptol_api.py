import unittest
from pathlib import Path
import os
from pathlib import Path
import subprocess
import time
import unittest
import signal
from shutil import which
import cryptol
import argo_client.connection as argo
from argo_client.interaction import ArgoException
import cryptol.cryptoltypes
from cryptol.single_connection import *
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import * #type: ignore


class CryptolTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))

    def test_low_level(self):
        x_val = cry_eval("x")

        self.assertEqual(cry_eval("Id::id x"), x_val)
        self.assertEqual(call('Id::id', bytes.fromhex('ff')), BV(8,255))

        self.assertEqual(call('add', b'\0', b'\1'), BV(8,1))
        self.assertEqual(call('add', bytes.fromhex('ff'), bytes.fromhex('03')), BV(8,2))

    # AMK: importing cryptol bindings into Python temporarily broken due to linear state usage changes
    # in argo approx 1 March 2020
    # def test_module_import(self):
    #     c = cryptol.connect()
    #     cryptol.add_cryptol_module('Foo', c)
    #     from Foo import add
    #     self.assertEqual(add(b'\2', 2), BV(8,4))

    #     self.assertEqual(add(BitVector( intVal = 0, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,1))
    #     self.assertEqual(add(BitVector( intVal = 1, size = 8 ), BitVector( intVal = 2, size = 8 )), BV(8,3))
    #     self.assertEqual(add(BitVector( intVal = 255, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,0))
    #     self.assertEqual(add(BV(8,0),   BV(8,1)), BV(8,1))
    #     self.assertEqual(add(BV(8,1),   BV(8,2)), BV(8,3))
    #     self.assertEqual(add(BV(8,255), BV(8,1)), BV(8,0))

    def test_sat_and_prove(self):
        # test a single sat model can be returned
        rootsOf9 = sat('isSqrtOf9')
        self.assertTrue(rootsOf9)
        self.assertEqual(len(rootsOf9.models), 1)
        self.assertEqual(len(rootsOf9.models[0]), 1)
        self.assertTrue(int(rootsOf9.models[0][0]) ** 2 % 256, 9)

        # check we can specify the solver
        rootsOf9 = sat('isSqrtOf9', solver = solver.ANY)
        self.assertTrue(rootsOf9)
        self.assertEqual(len(rootsOf9.models), 1)
        self.assertEqual(len(rootsOf9.models[0]), 1)
        self.assertTrue(int(rootsOf9.models[0][0]) ** 2 % 256, 9)

        # check we can ask for a specific number of results
        rootsOf9 = sat('isSqrtOf9', count = 3)
        self.assertTrue(rootsOf9)
        self.assertEqual(len(rootsOf9.models), 3)
        for model in rootsOf9.models:
            self.assertEqual(len(model), 1)
            self.assertTrue(int(model[0]) ** 2 % 256, 9)

        # check we can ask for all results
        rootsOf9 = sat('isSqrtOf9', count = None)
        self.assertTrue(rootsOf9)
        self.assertEqual(len(rootsOf9.models), 4)
        for model in rootsOf9.models:
            self.assertEqual(len(model), 1)
            self.assertTrue(int(model[0]) ** 2 % 256, 9)

        # check for an unsat condition
        self.assertFalse(sat('\\x -> isSqrtOf9 x && ~(elem x [3,131,125,253])'))

        # check for a valid condition
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]'))
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]', solver.Z3))
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]', solver.W4_Z3))
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]', solver.W4_Z3.without_hash_consing()))
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]', solver.SBV_Z3))
        self.assertIsInstance(prove('\\(x : [8]) -> x == reverse (reverse x)', solver.OFFLINE), solver.OfflineSmtQuery)
        self.assertIsInstance(prove('\\(x : [8]) -> x == reverse (reverse x)', solver.SBV_OFFLINE), solver.OfflineSmtQuery)
        self.assertIsInstance(prove('\\(x : [8]) -> x == reverse (reverse x)', solver.W4_OFFLINE), solver.OfflineSmtQuery)


    def test_check(self):
        res = check("\\x -> x==(x:[8])")
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 100)
        self.assertEqual(res.tests_possible, 256)
        self.assertFalse(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> x==(x:[8])", num_tests=1)
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 1)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> x==(x:[8])", num_tests=42)
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 42)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> x==(x:[8])", num_tests=1000)
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 256)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> x==(x:[8])", num_tests='all')
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 256)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> x==(x:Integer)", num_tests=1024)
        self.assertTrue(res.success)
        self.assertEqual(res.tests_run, 1024)
        self.assertEqual(res.tests_possible, None)
        self.assertEqual(len(res.args), 0)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> (x + 1)==(x:[8])")
        self.assertFalse(res.success)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 1)
        self.assertEqual(res.error_msg, None)

        res = check("\\x -> (x / 0)==(x:[8])")
        self.assertFalse(res.success)
        self.assertEqual(res.tests_possible, 256)
        self.assertEqual(len(res.args), 1)
        self.assertIsInstance(res.error_msg, str)

    def test_safe(self):
        res = safe("\\x -> x==(x:[8])")
        self.assertTrue(res)

        res = safe("\\x -> x / (x:[8])")
        self.assertFalse(res)
        self.assertEqual(res.assignments, [BV(size=8, value=0)])

        res = safe("\\x -> x / (x:[8])", solver.Z3)
        self.assertFalse(res)
        self.assertEqual(res.assignments, [BV(size=8, value=0)])

        res = safe("\\x -> x / (x:[8])", solver.W4_Z3)
        self.assertFalse(res)
        self.assertEqual(res.assignments, [BV(size=8, value=0)])


    def test_many_usages_one_connection(self):
        for i in range(0,100):
            x_val1 = cry_eval("x")
            x_val2 = cry_eval("Id::id x")
            self.assertEqual(x_val1, x_val2)



class HttpMultiConnectionTests(unittest.TestCase):
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
                server = which(server)
            if server is None:
                server = which('cryptol-remote-api')
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
            connect(url=self.url, verify=False)
            load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))
            x_val1 = cry_eval("x")
            x_val2 = cry_eval("Id::id x")
            self.assertEqual(x_val1, x_val2)
            reset()

    def test_server_with_many_usages_many_connections(self):
        for i in range(0,100):
            time.sleep(.05)
            connect(url=self.url, verify=False)
            load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))
            x_val1 = cry_eval("x")
            x_val2 = cry_eval("Id::id x")
            self.assertEqual(x_val1, x_val2)


class TLSConnectionTests(unittest.TestCase):
    # Python initiated process running the server (if any)
    p = None
    # url of HTTP server
    url = None
    run_tests = True

    @classmethod
    def setUpClass(self):
        os.system('openssl req -nodes -newkey rsa:2048 -keyout server.key -out server.csr'\
            + ' -subj "/C=GB/ST=London/L=London/O=Acme Widgets/OU=IT Department/CN=localhost"')
        os.system('openssl x509 -req -days 365 -in server.csr -signkey server.key -out server.crt')
        server = os.getenv('CRYPTOL_SERVER')
        if server is not None:
            server = which(server)
        if server is None:
            server = which('cryptol-remote-api')
        if server is not None:
            self.p = subprocess.Popen(
                [server, "http", "/", "--port", "8081", "--tls"],
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
            self.url = "https://localhost:8081/"
        else:
            print("WARNING: TLS tests not being run because no cryptol server executable was found")
            print("         (Note that this is expected behavior, however, for some CI tests)")
            self.run_tests = False

    @classmethod
    def tearDownClass(self):
        if self.p is not None:
            os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
        super().tearDownClass()

    def test_tls_connection(self):
        if self.run_tests:
            connect(url=self.url, verify=False)
            load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))
            x_val1 = cry_eval("x")
            x_val2 = cry_eval("Id::id x")
            self.assertEqual(x_val1, x_val2)


class CryptolParamModTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files', 'Param.cry')))

    def test_param_mod(self):
        with self.assertRaises(ArgoException) as res:
            check('foo')
        e = res.exception
        self.assertEqual(e.data['type parameters'], [])
        self.assertEqual(e.data['definitions'], ['Param::foo'])

        with self.assertRaises(ArgoException) as res:
            check('`(w)')
        e = res.exception
        self.assertEqual(e.data['type parameters'], ['Param::Param__parameter::w'])
        self.assertEqual(e.data['definitions'], [])


if __name__ == "__main__":
    unittest.main()
