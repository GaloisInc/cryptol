import unittest
from pathlib import Path
import unittest
import io
import cryptol
import cryptol.cryptoltypes
from cryptol.single_connection import *
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(verify=False)

    def test_extend_search_path(self):
      """Test that extending the search path acts as expected w.r.t. loads."""
      extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      load_module('Bar')
      ans1 = cry_eval("theAnswer")
      ans2 = cry_eval("id theAnswer")
      self.assertEqual(ans1, ans2)

    def test_logging(self):
      extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      load_module('Bar')

      log_buffer = io.StringIO()
      logging(on=True, dest=log_buffer)
      _ = cry_eval("theAnswer")
      contents = log_buffer.getvalue()
      print(f'CONTENTS: {contents}', file=sys.stderr)

      self.assertEqual(len(contents.strip().splitlines()), 2)

      _ = cry_eval("theAnswer")


class BasicLoggingServerTests(unittest.TestCase):
    # Connection to cryptol
    log_buffer = None

    @classmethod
    def setUpClass(self):
        self.log_buffer = io.StringIO()
        connect(verify=False, log_dest = self.log_buffer)

    def test_logging(self):
      extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      load_module('Bar')
      _ = cry_eval("theAnswer")

      self.assertEqual(len(self.log_buffer.getvalue().splitlines()), 6)

if __name__ == "__main__":
    unittest.main()
