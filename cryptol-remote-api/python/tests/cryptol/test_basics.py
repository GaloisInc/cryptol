import unittest
from pathlib import Path
import os
from pathlib import Path
import subprocess
import time
import unittest
import signal
from distutils.spawn import find_executable
import cryptol
import argo_client.connection as argo
import cryptol.cryptoltypes
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        self.c = cryptol.connect(verify=False)

    @classmethod
    def tearDownClass(self):
        if self.c:
            self.c.reset()

    def test_extend_search_path(self):
      """Test that extending the search path acts as expected w.r.t. loads."""
      c = self.c

      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')
      ans1 = c.evaluate_expression("theAnswer").result()
      ans2 = c.evaluate_expression("id theAnswer").result()
      self.assertEqual(ans1, ans2)

if __name__ == "__main__":
    unittest.main()
