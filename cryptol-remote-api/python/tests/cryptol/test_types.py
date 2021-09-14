import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.opaque import OpaqueValue
from cryptol.bitvector import BV


class CryptolTypeTests(unittest.TestCase):
    def test_types(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','Types.cry')))

        # Bits
        self.assertEqual(cry_eval('b'), True)
        
        # Words
        self.assertEqual(cry_eval('w'), BV(size=16, value=42))
        
        # Integers
        self.assertEqual(cry_eval('z'), 420000)
        
        # Modular integers - not supported at all
        with self.assertRaises(ValueError):
            cry_eval('m')

        # Rationals - supported only as opaque values
        self.assertIsInstance(cry_eval('q'), OpaqueValue)
    
        # Tuples
        self.assertEqual(cry_eval('t'), (False, 7))

        # Sequences
        self.assertEqual(cry_eval('s'),
            [[BV(size=8, value=1), BV(size=8, value=2), BV(size=8, value=3)],
             [BV(size=8, value=4), BV(size=8, value=5), BV(size=8, value=6)],
             [BV(size=8, value=7), BV(size=8, value=8), BV(size=8, value=9)]])
        
        # Records
        self.assertEqual(cry_eval('r'),
            {'xCoord': BV(size=32, value=12),
             'yCoord': BV(size=32, value=21)})

if __name__ == "__main__":
    unittest.main()
