import unittest
from pathlib import Path
import unittest
import cryptol
from cryptol.single_connection import *

def names_dict_to_names(names_dict, *, module):
    return [ {"module": module, "name": n, **vs} for n,vs in names_dict.items() ]

def filter_names(names, *, module, fields_to_exclude):
    return [ { k:v for k,v in n.items() if k not in fields_to_exclude } for n in names if n["module"] == module ]

class TestNames(unittest.TestCase):
    def test_names(self):
        connect(verify=False)
        load_file(str(Path('tests','cryptol','test-files', 'Names.cry')))

        # names()

        expected_names_dict = {
            'key': {'parameter': True},
            'enc': {},
            'enc_correct': {'pragmas': ['property']},
            'prim': {},
            '(-!)': {'infix': True, 'infix associativity': 'left-associative', 'infix level': 100}
        }
        expected_names = names_dict_to_names(expected_names_dict, module="Names")

        names_to_check = filter_names(names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_names, names_to_check)

        # property_names()

        expected_props_dict = {
            "enc_correct": expected_names_dict["enc_correct"]
        }
        expected_props = names_dict_to_names(expected_props_dict, module="Names")

        props_to_check = filter_names(property_names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_props, props_to_check)

        # parameter_names()

        expected_params_dict = {
            "key": expected_names_dict["key"]
        }
        expected_params = names_dict_to_names(expected_params_dict, module="Names")
        
        params_to_check = filter_names(parameter_names(), module="Names", fields_to_exclude=["type", "type string"])

        self.assertCountEqual(expected_params, params_to_check)

if __name__ == "__main__":
    unittest.main()
