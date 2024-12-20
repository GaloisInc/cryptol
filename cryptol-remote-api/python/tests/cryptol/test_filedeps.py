import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *


class TestFileDeps(unittest.TestCase):
    def test_FileDeps(self) -> None:
        connect(verify=False)
        path = str(Path('tests','cryptol','test-files','Id.cry'))
        result = file_deps(path,True)
        self.assertEqual(result['fingerprint'],"8316fb4e38d33ec3b9f89d355597c058b2e4baf653bf18dc4ead7e166a8a32f8")
        self.assertEqual(result['foreign'],[])
        self.assertEqual(result['imports'],['Cryptol'])
        self.assertEqual(result['includes'],[])
        # we don't check source because it is system dependent

if __name__ == "__main__":
    unittest.main()
