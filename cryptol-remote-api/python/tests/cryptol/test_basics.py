import unittest
from pathlib import Path
import unittest
import io
import cryptol
import cryptol.cryptoltypes
from cryptol.bitvector import BV
from BitVector import * #type: ignore


# Tests of the core server functionality and less
# focused on intricate Cryptol specifics per se.

class BasicServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        self.c = cryptol.connect_sync(verify=False)

    @classmethod
    def tearDownClass(self):
        if self.c:
            self.c.reset()

    def test_extend_search_path(self):
      """Test that extending the search path acts as expected w.r.t. loads."""
      c = self.c

      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')
      ans1 = c.eval("theAnswer")
      ans2 = c.eval("id theAnswer")
      self.assertEqual(ans1, ans2)

    def test_logging(self):
      c = self.c
      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')

      log_buffer = io.StringIO()
      c.logging(on=True, dest=log_buffer)
      _ = c.eval("theAnswer")
      contents = log_buffer.getvalue()
      print(f'CONTENTS: {contents}', file=sys.stderr)

      self.assertEqual(len(contents.strip().splitlines()), 2)

      _ = c.eval("theAnswer")


class BasicLoggingServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None
    log_buffer = None

    @classmethod
    def setUpClass(self):
        self.log_buffer = io.StringIO()
        self.c = cryptol.connect_sync(verify=False, log_dest = self.log_buffer)

    @classmethod
    def tearDownClass(self):
        if self.c:
            self.c.reset()

    def test_logging(self):
      c = self.c
      c.extend_search_path(str(Path('tests','cryptol','test-files', 'test-subdir')))
      c.load_module('Bar')
      _ = c.eval("theAnswer")

      self.assertEqual(len(self.log_buffer.getvalue().splitlines()), 6)

if __name__ == "__main__":
    unittest.main()
