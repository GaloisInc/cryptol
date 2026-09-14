import unittest
from pathlib import Path
import cryptol
from cryptol.single_connection import *

class TestProjectNestedModuleHierarchy(unittest.TestCase):
    def test_project_nested_module_hierarchy(self):
        connect(verify=False)
        res = load_project(str(Path('tests','cryptol','test-files','project-nested-module-hierarchy')), 'untested')
        print('LOAD', res)
        print('MODULES', modules())
        print('FOCUS', focus_module("A::B"))
        print('CHECK', check_docstrings(res["cache_id"]))

if __name__ == "__main__":
    unittest.main()
