import os
import distutils.spawn
import unittest
from cryptol import CryptolConnection, CryptolContext, cry
import cryptol
import cryptol.cryptoltypes
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import *

def exe_exists(name : str) -> bool:
    return distutils.spawn.find_executable(name) is not None

dir_path = os.path.dirname(os.path.realpath(__file__))

class CryptolTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        if exe_exists("cryptol-remote-api"):
            self.c = cryptol.connect("cryptol-remote-api socket")
        else:
            self.c = cryptol.connect("cabal run --verbose=0 exe:cryptol-remote-api -- socket")

        self.c.change_directory(dir_path)

        self.c.load_file("Foo.cry")

    def test_low_level(self):
        c = self.c
        x_val = c.evaluate_expression("x").result()

        self.assertEqual(c.evaluate_expression("Id::id x").result(), x_val)
        self.assertEqual(c.call('Id::id', bytes.fromhex('ff')).result(), BV(8,255))

        self.assertEqual(c.call('add', b'\0', b'\1').result(), BV(8,1))
        self.assertEqual(c.call('add', bytes.fromhex('ff'), bytes.fromhex('03')).result(), BV(8,2))

    def test_module_import(self):
        c = self.c
        cryptol.add_cryptol_module('Foo', c)
        from Foo import add
        self.assertEqual(add(b'\2', 2), BV(8,4))

        self.assertEqual(add(BitVector( intVal = 0, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,1))
        self.assertEqual(add(BitVector( intVal = 1, size = 8 ), BitVector( intVal = 2, size = 8 )), BV(8,3))
        self.assertEqual(add(BitVector( intVal = 255, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,0))
        self.assertEqual(add(BV(8,0),   BV(8,1)), BV(8,1))
        self.assertEqual(add(BV(8,1),   BV(8,2)), BV(8,3))
        self.assertEqual(add(BV(8,255), BV(8,1)), BV(8,0))

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

