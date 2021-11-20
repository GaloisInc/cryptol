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


if __name__ == "__main__":
    unittest.main()
