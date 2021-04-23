import unittest
from pathlib import Path
import os
from pathlib import Path
import subprocess
import time
import unittest
import signal
from distutils.spawn import find_executable
from cryptol.scryptol import *
import argo_client.connection as argo
import cryptol.cryptoltypes
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import * #type: ignore


class CryptolTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)
        load_file(str(Path('tests','cryptol','test-files', 'Foo.cry')))

    @classmethod
    def tearDownClass(self):
        if connected():
            reset()

    def test_low_level(self):
        x_val = evaluate_expression("x")

        self.assertEqual(eval("Id::id x"), x_val)
        self.assertEqual(call('Id::id', bytes.fromhex('ff')), BV(8,255))

        self.assertEqual(call('add', b'\0', b'\1'), BV(8,1))
        self.assertEqual(call('add', bytes.fromhex('ff'), bytes.fromhex('03')), BV(8,2))

    # AMK: importing cryptol bindings into Python temporarily broken due to linear state usage changes
    # in argo approx 1 March 2020
    # def test_module_import(self):
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
        # test a single sat model can be returned
        rootsOf9 = sat('isSqrtOf9')
        self.assertEqual(len(rootsOf9), 1)
        self.assertTrue(int(rootsOf9[0]) ** 2 % 256, 9)

        # check we can specify the solver
        rootsOf9 = sat('isSqrtOf9', solver = solver.ANY)
        self.assertEqual(len(rootsOf9), 1)
        self.assertTrue(int(rootsOf9[0]) ** 2 % 256, 9)

        # check we can ask for a specific number of results
        rootsOf9 = sat('isSqrtOf9', count = 3)
        self.assertEqual(len(rootsOf9), 3)
        self.assertEqual([int(root) ** 2 % 256 for root in rootsOf9], [9,9,9])

        # check we can ask for all results
        rootsOf9 = sat('isSqrtOf9', count = None)
        self.assertEqual(len(rootsOf9), 4)
        self.assertEqual([int(root) ** 2 % 256 for root in rootsOf9], [9,9,9,9])

        # check for an unsat condition
        self.assertFalse(sat('\\x -> isSqrtOf9 x && ~(elem x [3,131,125,253])'))

        # check for a valid condition
        self.assertTrue(prove('\\x -> isSqrtOf9 x ==> elem x [3,131,125,253]'))

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
        self.assertEqual(res, [BV(size=8, value=0)])


    def test_many_usages_one_connection(self):
        for i in range(0,100):
            x_val1 = evaluate_expression("x")
            x_val2 = eval("Id::id x")
            self.assertEqual(x_val1, x_val2)



if __name__ == "__main__":
    unittest.main()
