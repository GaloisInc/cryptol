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
        load_file(str(Path('tests','cryptol','test-files', 'Names.cry')))

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

if __name__ == "__main__":
    unittest.main()
