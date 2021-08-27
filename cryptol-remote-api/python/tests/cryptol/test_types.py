import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.opaque import OpaqueValue
from cryptol.bitvector import BV


class CryptolTypeTests(unittest.TestCase):
    def test_types(self):
        c = cryptol.connect_sync(verify=False)
        c.load_file(str(Path('tests','cryptol','test-files','Types.cry')))

        # Bits
        self.assertEqual(c.eval('b'), True)
        
        # Words
        self.assertEqual(c.eval('w'), BV(size=16, value=42))
        
        # Integers
        self.assertEqual(c.eval('z'), 420000)
        
        # Modular integers - not supported at all
        with self.assertRaises(ValueError):
            c.eval('m')

        # Rationals - supported only as opaque values
        self.assertIsInstance(c.eval('q'), OpaqueValue)
    
        # Tuples
        self.assertEqual(c.eval('t'), (False, 7))

        # Sequences
        self.assertEqual(c.eval('s'),
            [[BV(size=8, value=1), BV(size=8, value=2), BV(size=8, value=3)],
             [BV(size=8, value=4), BV(size=8, value=5), BV(size=8, value=6)],
             [BV(size=8, value=7), BV(size=8, value=8), BV(size=8, value=9)]])
        
        # Records
        self.assertEqual(c.eval('r'),
            {'xCoord': BV(size=32, value=12),
             'yCoord': BV(size=32, value=21)})

if __name__ == "__main__":
    unittest.main()
