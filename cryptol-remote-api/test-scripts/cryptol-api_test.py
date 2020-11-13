import os
import unittest
from cryptol import CryptolConnection, CryptolContext, cry
import cryptol
import cryptol.cryptoltypes
from cryptol.bitvector import BV
from BitVector import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = cryptol.connect("cabal new-exec --verbose=0 cryptol-remote-api -- socket")

c.change_directory(dir_path)

c.load_file("Foo.cry")

class CryptolTests(unittest.TestCase):

    def test_low_level(self):
        x_val = c.evaluate_expression("x").result()

        self.assertEqual(c.evaluate_expression("Id::id x").result(), x_val)
        self.assertEqual(c.call('Id::id', bytes.fromhex('ff')).result(), BV(8,255))

        self.assertEqual(c.call('add', b'\0', b'\1').result(), BV(8,1))
        self.assertEqual(c.call('add', bytes.fromhex('ff'), bytes.fromhex('03')).result(), BV(8,2))

    def test_module_import(self):
        cryptol.add_cryptol_module('Foo', c)
        from Foo import add
        self.assertEqual(add(b'\2', 2), BV(8,4))

        self.assertEqual(add(BitVector( intVal = 0, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,1))
        self.assertEqual(add(BitVector( intVal = 1, size = 8 ), BitVector( intVal = 2, size = 8 )), BV(8,3))
        self.assertEqual(add(BitVector( intVal = 255, size = 8 ), BitVector( intVal = 1, size = 8 )), BV(8,0))
        self.assertEqual(add(BV(8,0),   BV(8,1)), BV(8,1))
        self.assertEqual(add(BV(8,1),   BV(8,2)), BV(8,3))
        self.assertEqual(add(BV(8,255), BV(8,1)), BV(8,0))


unittest.main()
