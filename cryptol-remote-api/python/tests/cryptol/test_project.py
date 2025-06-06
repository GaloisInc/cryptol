import unittest
from pathlib import Path
import cryptol
from cryptol.single_connection import *

class TestProject(unittest.TestCase):
    def test_project(self):
        connect(verify=False)
        res = load_project(str(Path('tests','cryptol','test-files')), 'untested')
        print('LOAD', res)
        print('MODULES', modules())
        print('FOCUS', focus_module("Id"))
        print('CHECK', check_docstrings(res["cache_id"]))

if __name__ == "__main__":
    unittest.main()
