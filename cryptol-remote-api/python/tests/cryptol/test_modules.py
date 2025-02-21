import unittest
from pathlib import Path
import cryptol
from cryptol.single_connection import *

class TestModules(unittest.TestCase):
    def test_modules(self):
        connect(verify=False)

        load_file(str(Path('tests','cryptol','test-files', 'Modules.cry')))
        expected = [
            {'module': 'Cryptol', 'parameterized': False},
            {'module': 'Modules', 'parameterized': False, 'documentation': ['A top-level\ndocstring\n']},
            {'module': 'Modules::where_at__17_11', 'parameterized': False},
            {'module': 'Modules::M', 'parameterized': False, 'documentation': ['A submodule docstring\n', 'A functor docstring\n']},
            {'module': 'Modules::M::Q', 'parameterized': False, 'documentation': ['A submodule in a functor docstring\n']},
            {'module': 'Modules::F', 'parameterized': True, 'documentation': ['A functor docstring\n']},
            {'module': 'Modules::F::Q', 'parameterized': True, 'documentation': ['A submodule in a functor docstring\n']},
        ]
        names_to_check = modules()
        self.assertCountEqual(expected, names_to_check)
        
        load_file(str(Path('tests','cryptol','test-files', 'Param.cry')))
        expected = [
            {'module': 'Param', 'parameterized': True},
            {'module': 'Cryptol', 'parameterized': False},
        ]
        names_to_check = modules()
        self.assertCountEqual(expected, names_to_check)


if __name__ == "__main__":
    unittest.main()
