import unittest
from pathlib import Path
import os
from pathlib import Path
import subprocess
import time
import unittest
import signal
from distutils.spawn import find_executable
from cryptol.scryptol import *
import argo_client.connection as argo
import cryptol.cryptoltypes
from cryptol import solver
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        if connected():
            reset()

    def test_extend_search_path(self):
      """Test that extending the search path acts as expected w.r.t. loads."""
      extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      load_module('Bar')
      ans1 = evaluate_expression("theAnswer")
      ans2 = evaluate_expression("id theAnswer")
      self.assertEqual(ans1, ans2)

if __name__ == "__main__":
    unittest.main()
