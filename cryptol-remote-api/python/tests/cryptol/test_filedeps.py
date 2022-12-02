import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *

class TestFileDeps(unittest.TestCase):
    def test_FileDeps(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files','Id.cry')))
        result = file_deps('Id',False)
        self.assertEqual(result['fingerprint'],"8A49C6A461AF276DF56C4FE4279BCFC51D891214")
        self.assertEqual(result['foreign'],[])
        self.assertEqual(result['imports'],['Cryptol'])
        self.assertEqual(result['includes'],[])
        # we don't check source because it is system dependent

if __name__ == "__main__":
    unittest.main()
