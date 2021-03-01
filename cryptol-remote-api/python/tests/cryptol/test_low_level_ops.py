import os
from pathlib import Path
import signal
import subprocess
import time
import unittest

import argo_client.connection as argo
import cryptol
from distutils.spawn import find_executable

# cryptol_path = dir_path.joinpath('data')

# Test empty options
def do_test_options(c, state, options):
    id_opt = c.send_query("evaluate expression", {"state": state, "expression": "four", "options": options})
    reply_opt = c.wait_for_reply_to(id_opt)
    assert('result' in reply_opt)
    assert('answer' in reply_opt['result'])
    assert('value' in reply_opt['result']['answer'])
    assert(reply_opt['result']['answer']['value'] == {'data': '00004', 'width': 17, 'expression': 'bits', 'encoding': 'hex'})

def do_test_instantiation(c, state, t, expected=None):
    if expected is None: expected = t
    id_t = c.send_query("check type", {"state": state, "expression": {"expression": "instantiate", "generic": "id", "arguments": {"a": t}}})
    reply_t = c.wait_for_reply_to(id_t)
    assert('result' in reply_t)
    assert('answer' in reply_t['result'])
    assert('type schema' in reply_t['result']['answer'])
    assert(reply_t['result']['answer']['type schema']['type']['domain'] == expected)

class LowLevelCryptolApiTests(unittest.TestCase):
    c = None

    @classmethod
    def setUpClass(self):
        if (command := os.getenv('CRYPTOL_SERVER')) is not None and (command := find_executable(command)) is not None:
            self.c = argo.ServerConnection(argo.DynamicSocketProcess(command + " socket"))
        elif (url := os.getenv('CRYPTOL_SERVER_URL')) is not None:
            self.c = argo.ServerConnection(argo.HttpProcess(url))
        elif (command := find_executable('cryptol-remote-api')) is not None:
            self.c = argo.ServerConnection(argo.StdIOProcess(command + " stdio"))
        else:
            raise RuntimeError("NO CRYPTOL SERVER FOUND")

    def test_low_level_api(self):
        c = self.c

        id_1 = c.send_command("load file", {"file": str(Path('tests','cryptol','test-files', 'M.cry')), "state": None})
        reply_1 = c.wait_for_reply_to(id_1)
        self.assertIn('result', reply_1)
        self.assertIn('state', reply_1['result'])
        self.assertIn('answer', reply_1['result'])
        state_1 = reply_1['result']['state']
 
        id_2 = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"f","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state_1})
        reply_2 = c.wait_for_reply_to(id_2)
        self.assertIn('result', reply_2)
        self.assertIn('answer', reply_2['result'])
        self.assertIn('value', reply_2['result']['answer'])
        self.assertEqual(reply_2['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
 
        id_3 = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"g","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state_1})
        reply_3 = c.wait_for_reply_to(id_3)
        self.assertIn('result', reply_3)
        self.assertIn('answer', reply_3['result'])
        self.assertIn('value', reply_3['result']['answer'])
        self.assertEqual(reply_3['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
 
        id_4 = c.send_query("evaluate expression", {"expression":{"expression":"call","function":"h","arguments":[{"expression":"sequence","data":[{"expression":"bits","encoding":"hex","data":"ff","width":8},{"expression":"bits","encoding":"hex","data":"ff","width":8}]}]}, "state": state_1})
        reply_4 = c.wait_for_reply_to(id_4)
        self.assertIn('result', reply_4)
        self.assertIn('answer', reply_4['result'])
        self.assertIn('value', reply_4['result']['answer'])
        self.assertEqual(reply_4['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
 
        a_record = {"expression": "record",
                      "data": {"unit": "()",
                             "fifteen": {"expression": "bits",
                                           "encoding": "hex",
                                           "width": 4,
                                           "data": "f"}}}
 
        id_5 = c.send_query("evaluate expression", {"state": state_1, "expression": a_record})
        reply_5 = c.wait_for_reply_to(id_5)
        self.assertIn('result', reply_5)
        self.assertIn('answer', reply_5['result'])
        self.assertIn('value', reply_5['result']['answer'])
        self.assertEqual(reply_5['result']['answer']['value'],
               {'expression': 'record',
               'data': {'fifteen':
                             {'data': 'f',
                             'width': 4,
                             'expression': 'bits',
                             'encoding': 'hex'},
                             'unit':
                             {'expression': 'unit'}}})
 
        id_6 = c.send_query("evaluate expression",
                             {"state": state_1,
                             "expression": {"expression": "let",
                                                  "binders": [{"name": "theRecord", "definition": a_record}],
                                                  "body": {"expression": "tuple",
                                                         "data": [a_record, "theRecord"]}}})
        reply_6 = c.wait_for_reply_to(id_6)
        self.assertIn('result', reply_6)
        self.assertIn('answer', reply_6['result'])
        self.assertIn('value', reply_6['result']['answer'])
        self.assertEqual(reply_6['result']['answer']['value'],
               {'expression': 'tuple',
               'data': [{'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'},
                             {'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'}]})
 
        id_7 = c.send_query("evaluate expression",
                             {"state": state_1,
                             "expression": {"expression": "sequence",
                                                  "data": [a_record, a_record]}})
        reply_7 = c.wait_for_reply_to(id_7)
        self.assertIn('result', reply_7)
        self.assertIn('answer', reply_7['result'])
        self.assertIn('value', reply_7['result']['answer'])
        self.assertEqual(reply_7['result']['answer']['value'],
               {'expression': 'sequence',
               'data': [{'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'},
                             {'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'}]})
 
        id_8 = c.send_query("evaluate expression",
                             {"state": state_1,
                             "expression": {"expression": "integer modulo",
                                                  "integer": 14,
                                                  "modulus": 42}})
        reply_8 = c.wait_for_reply_to(id_8)
        self.assertIn('result', reply_8)
        self.assertIn('answer', reply_8['result'])
        self.assertIn('value', reply_8['result']['answer'])
        self.assertEqual(reply_8['result']['answer']['value'],
               {"expression": "integer modulo",
               "integer": 14,
               "modulus": 42})
 
        id_9 = c.send_query("evaluate expression",
                             {"state": state_1,
                             "expression": "m `{a=60}"})
        reply_9 = c.wait_for_reply_to(id_9)
        self.assertIn('result', reply_9)
        self.assertIn('answer', reply_9['result'])
        self.assertIn('value', reply_9['result']['answer'])
        self.assertEqual(reply_9['result']['answer']['value'],
               {"expression": "integer modulo",
               "integer": 42,
               "modulus": 60})
 
 
        id_10 = c.send_query("evaluate expression", {"state": state_1, "expression": "two"})
        reply_10 = c.wait_for_reply_to(id_10)
        self.assertIn('result', reply_10)
        self.assertIn('answer', reply_10['result'])
        self.assertIn('value', reply_10['result']['answer'])
        self.assertEqual(reply_10['result']['answer']['value'], {'data': '0002', 'width': 15, 'expression': 'bits', 'encoding': 'hex'})
 
        id_11 = c.send_query("evaluate expression", {"state": state_1, "expression": "three"})
        reply_11 = c.wait_for_reply_to(id_11)
        self.assertIn('result', reply_11)
        self.assertIn('answer', reply_11['result'])
        self.assertIn('value', reply_11['result']['answer'])
        self.assertEqual(reply_11['result']['answer']['value'], {'data': '0003', 'width': 16, 'expression': 'bits', 'encoding': 'hex'})
 
        id_12 = c.send_query("evaluate expression", {"state": state_1, "expression": "four"})
        reply_12 = c.wait_for_reply_to(id_12)
        self.assertIn('result', reply_12)
        self.assertIn('answer', reply_12['result'])
        self.assertIn('value', reply_12['result']['answer'])
        self.assertEqual(reply_12['result']['answer']['value'], {'data': '00004', 'width': 17, 'expression': 'bits', 'encoding': 'hex'})

        do_test_options(c, state_1, dict())
        do_test_options(c, state_1, {"call stacks": True})
        do_test_options(c, state_1, {"call stacks": False})
        do_test_options(c, state_1, {"call stacks": False, "output": dict()})
        do_test_options(c, state_1, {"call stacks": False, "output": {"ASCII": True}})
        do_test_options(c, state_1, {"call stacks": False, "output": {"base": 16}})
        do_test_options(c, state_1, {"call stacks": False, "output": {"prefix of infinite lengths": 3}})

        # These test both the type instantiation form and the serialization/deserialization of the types involved
        do_test_instantiation(c, state_1, {"type": "Integer"})
        do_test_instantiation(c, state_1, {"type": "record",
                             "fields": {'a': {'type': 'Integer'},
                                           'b': {'type': 'sequence', 'length': {'type': 'inf'}, 'contents': {'type': 'unit'}}}})
        do_test_instantiation(c, state_1, {'type': 'sequence',
                             'length': {'type': 'number', 'value': 42},
                             'contents': {'type': 'Rational'}})
        do_test_instantiation(c, state_1, {'type': 'bitvector',
                             'width': {'type': 'number', 'value': 432}})
        do_test_instantiation(c, state_1, {'type': 'variable',
                             'name': 'Word8'},
                             {'type': 'bitvector',
                             'width': {'type': 'number', 'value': 8}})
        do_test_instantiation(c, state_1, {'type': 'variable',
                             'name': 'Twenty',
                             'arguments': [{'type': 'Z', 'modulus': {'type': 'number', 'value': 5}}]},
                             { 'type': 'sequence',
                             'length': {'value': 20, 'type': 'number'},
                             'contents': {'type': 'Z', 'modulus': {'value': 5, 'type': 'number'}}})

if __name__ == "__main__":
    unittest.main()





# class RemoteSockeLowLevelCryptolApiTests(GenericLowLevelCryptolApiTests, unittest.TestCase):
#     p = None

#     @classmethod
#     def setUpClass(self):
#         env = os.environ.copy()
#         env['CRYPTOLPATH'] = cryptol_path

#         if find_executable("cryptol-remote-api"):
#             p = subprocess.Popen(
#                 ["cryptol-remote-api", "socket", "--port", "50005"],
#                 stdout=subprocess.DEVNULL,
#                 stdin=subprocess.DEVNULL,
#                 stderr=subprocess.DEVNULL,
#                 start_new_session=True,
#                 env=env)
#         else:
#             raise RuntimeError('Failed to find cryptol-remote-api executable in PATH')

#         time.sleep(5)
#         assert(p is not None)
#         poll_result = p.poll()
#         if poll_result is not None:
#             print(poll_result)
#             print(p.stdout.read())
#             print(p.stderr.read())
#         assert(poll_result is None)
#         self.p = p

#         self.c = argo.ServerConnection(argo.RemoteSocketProcess('localhost', 50005, ipv6=True))

#     @classmethod
#     def tearDownClass(self):
#         os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
#         super().tearDownClass()

#     # to be implemented by classes extending this one
#     def get_connection(self):
#         return self.c
