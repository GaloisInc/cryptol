import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *
from cryptol.bitvector import BV
from cryptol.quoting import *

class TestQuoting(unittest.TestCase):
    def test_quoting(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files', 'M.cry')))

        x = BV(size=8, value=1)
        y = cry_f('g {x}')
        z = cry_f('h {y}')
        self.assertEqual(z, cry('h (g 0x01)'))
        self.assertEqual(cry_eval(z), [x,x])

        y = cry_eval_f('g {x}')
        z = cry_eval_f('h {y}')
        self.assertEqual(y, [x,x])
        self.assertEqual(z, [x,x])

        self.assertEqual(cry_f('id {BV(size=7, value=1)}'), cry('id (1 : [7])'))
        self.assertEqual(cry_eval_f('id {BV(size=7, value=1)}'), BV(size=7, value=1))

        self.assertEqual(cry_f('{ {"a": x, "b": x} }'), cry('{a = 0x01, b = 0x01}'))
        self.assertEqual(cry_f('{{a = {x}, b = {x}}}'), cry('{a = 0x01, b = 0x01}'))

        self.assertEqual(cry_f('id {5}'),       cry('id 5'))
        self.assertEqual(cry_f('id {5!s}'),     cry('id ([53] : [1][8])')) # id "5"
        self.assertEqual(cry_f('id {5:#x}'),    cry('id ([48, 120, 53] : [3][8])')) # id "0x5"
        self.assertEqual(cry_f('id {BV(4,5)}'), cry('id 0x5'))

        s = '" \n ÿ \\'
        self.assertEqual(cry_f('{s}'), cry('([34, 32, 10, 32, 255, 32, 92] : [7][8])')) # "\" \n ÿ \\"
        self.assertEqual(cry_eval_f('{s}'), [BV(8,c) for c in [34, 32, 10, 32, 255, 32, 92]])
        with self.assertRaises(UnicodeEncodeError):
            cry_f('{"π"}') # 'latin-1' codec can't encode character (960 >= 256)

        # Only here to check backwards compatability, the above syntax is preferred
        y = cry('g')(cry_f('{x}'))
        z = cry('h')(cry_f('{y}'))
        self.assertEqual(str(z), str(cry('(h) ((g) (0x01))')))
        self.assertEqual(cry_eval(z), [x,x])
        self.assertEqual(str(cry('id')(cry_f('{BV(size=7, value=1)}'))), str(cry('(id) (1 : [7])')))
        # This is why this syntax is not preferred
        with self.assertRaises(ValueError):
            cry('g')(x) # x is not CryptolJSON


if __name__ == "__main__":
    unittest.main()
