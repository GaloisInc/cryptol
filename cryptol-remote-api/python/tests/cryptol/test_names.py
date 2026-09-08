import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *

def filter_names(names, *, module, fields_to_exclude):
    return [ { k:v for k,v in n.items() if k not in fields_to_exclude } for n in names if n["module"] == module ]

class TestNames(unittest.TestCase):
    def test_names(self):
        connect(verify=False)
        names_path = Path('tests','cryptol','test-files', 'Names.cry')
        load_file(str(names_path))

        # names()

        expected_names = [
            {'module': 'Names', 'name': 'key', 'parameter': () },
            {'module': 'Names', 'name': 'enc' },
            {'module': 'Names', 'name': 'enc_correct', 'pragmas': ['property'] },
            {'module': 'Names', 'name': 'prim' },
            {'module': 'Names', 'name': '(-!)', 'infix': {'associativity': 'left-associative', 'level': 100} }
        ]

        names_to_check = filter_names(names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_names, names_to_check)

        # property_names()

        prop_names = ['enc_correct']
        expected_props = [ n for n in expected_names if n['name'] in prop_names ]

        props_to_check = filter_names(property_names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_props, props_to_check)

        # parameter_names()

        param_names = ['key']
        expected_params = [ n for n in expected_names if n['name'] in param_names ]

        params_to_check = filter_names(parameter_names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_params, params_to_check)

        # name_location()

        source = str(names_path)
        self.assertEqual(
            [{'namespace': 'value', 'location': source, 'line': 9, 'column': 1}],
            name_location('enc'))
        self.assertEqual(
            [{'namespace': 'type', 'location': source, 'line': 23, 'column': 6}],
            name_location('b'))
        self.assertEqual(
            [{'namespace': 'module', 'location': source, 'line': 31, 'column': 11}],
            name_location('M'))

if __name__ == "__main__":
    unittest.main()
