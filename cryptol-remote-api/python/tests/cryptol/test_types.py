import unittest
from argo_client.interaction import ArgoException
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.opaque import OpaqueValue
from cryptol.bitvector import BV
from cryptol import cryptoltypes


class CryptolTypeTests(unittest.TestCase):
    def test_types(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','Types.cry')))

        # Bits
        self.assertEqual(cry_eval('b'), True)
        self.assertEqual(check_type('b'), cryptoltypes.Bit())
        
        # Words
        self.assertEqual(cry_eval('w'), BV(size=16, value=42))
        self.assertEqual(check_type('w'), cryptoltypes.Bitvector(cryptoltypes.Num(16)))
        
        # Integers
        self.assertEqual(cry_eval('z'), 420000)
        self.assertEqual(check_type('z'), cryptoltypes.Integer())
        
        # Modular integers - not supported as values
        with self.assertRaises(ValueError):
            cry_eval('m')
        self.assertEqual(check_type('m'), cryptoltypes.Z(cryptoltypes.Num(12)))

        # Rationals - supported only as opaque values
        self.assertIsInstance(cry_eval('q'), OpaqueValue)
        self.assertEqual(check_type('q'), cryptoltypes.Rational())
    
        # Tuples
        self.assertEqual(cry_eval('t'), (False, 7))
        t_ty = cryptoltypes.Tuple(cryptoltypes.Bit(), cryptoltypes.Integer())
        self.assertEqual(check_type('t'), t_ty)

        # Sequences
        self.assertEqual(cry_eval('s'),
            [[BV(size=8, value=1), BV(size=8, value=2), BV(size=8, value=3)],
             [BV(size=8, value=4), BV(size=8, value=5), BV(size=8, value=6)],
             [BV(size=8, value=7), BV(size=8, value=8), BV(size=8, value=9)]])
        s_ty = cryptoltypes.Sequence(cryptoltypes.Num(3),
               cryptoltypes.Sequence(cryptoltypes.Num(3),
               cryptoltypes.Bitvector(cryptoltypes.Num(8))))
        self.assertEqual(check_type('s'), s_ty)
        
        # Records
        self.assertEqual(cry_eval('r'),
            {'xCoord': BV(size=32, value=12),
             'yCoord': BV(size=32, value=21)})
        r_ty = cryptoltypes.Record({
          'xCoord': cryptoltypes.Bitvector(cryptoltypes.Num(32)),
          'yCoord': cryptoltypes.Bitvector(cryptoltypes.Num(32))})
        self.assertEqual(check_type('r'), r_ty)

        # Functions - not supported as values
        with self.assertRaises(ArgoException):
            cry_eval('id')
        n = cryptoltypes.Var('n', 'Num')
        id_ty = cryptoltypes.CryptolTypeSchema(
          {n.name: n.kind}, [cryptoltypes.PropCon('fin', n)],
          cryptoltypes.Function(cryptoltypes.Bitvector(n),
                                cryptoltypes.Bitvector(n)))
        self.assertEqual(check_type('id'), id_ty)
        

if __name__ == "__main__":
    unittest.main()
