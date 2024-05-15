import os
from pathlib import Path
import signal
import subprocess
import time
import unittest

import argo_client.connection as argo
import cryptol
from shutil import which

# cryptol_path = dir_path.joinpath('data')

# Test empty options
def do_test_options(test : unittest.TestCase, c, state, options):
    id_opt = c.send_command("evaluate expression", {"state": state, "expression": "four", "options": options})
    reply = c.wait_for_reply_to(id_opt)
    test.assertIn('result', reply)
    test.assertIn('answer', reply['result'])
    test.assertIn('value', reply['result']['answer'])
    test.assertEqual(reply['result']['answer']['value'], {'data': '00004', 'width': 17, 'expression': 'bits', 'encoding': 'hex'})
    return reply['result']['state']

def do_test_instantiation(test : unittest.TestCase, c, state, t, expected=None):
    if expected is None: expected = t
    id_t = c.send_command("check type", {"state": state, "expression": {"expression": "instantiate", "generic": "id", "arguments": {"a": t}}})
    reply = c.wait_for_reply_to(id_t)
    test.assertIn('result', reply)
    test.assertIn('result', reply)
    test.assertIn('answer', reply['result'])
    test.assertIn('type schema', reply['result']['answer'])
    test.assertEqual(reply['result']['answer']['type schema']['type']['domain'], expected)
    return reply['result']['state']

class LowLevelCryptolApiTests(unittest.TestCase):
    c = None

    @classmethod
    def setUpClass(self):
        server = os.getenv('CRYPTOL_SERVER')
        if server:
            server = which(server)
            if server:
                self.c = argo.ServerConnection(argo.DynamicSocketProcess(server + " socket"))
            else:
                raise RuntimeError(f'CRYPTOL_SERVER executable {server} could not be found')
        else:
            server = os.getenv('CRYPTOL_SERVER_URL')
            if server:
                self.c = argo.ServerConnection(argo.HttpProcess(server, verify=False))
            else:
                server = which('cryptol-remote-api')
                if server:
                    self.c = argo.ServerConnection(argo.StdIOProcess(server + " stdio"))
                else:
                    raise RuntimeError("NO CRYPTOL SERVER FOUND")

    def test_low_level_api(self):
        c = self.c

        uid = c.send_command("load file", {"file": str(Path('tests','cryptol','test-files', 'M.cry')), "state": None})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('state', reply['result'])
        self.assertIn('answer', reply['result'])
        state = reply['result']['state']

        uid = c.send_command("evaluate expression", {"expression": {"expression":"call","function":"f","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression", {"expression": {"expression":"call","function":"g","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression", {"expression":{"expression":"call","function":"h","arguments":[{"expression":"sequence","data":[{"expression":"bits","encoding":"hex","data":"ff","width":8},{"expression":"bits","encoding":"hex","data":"ff","width":8}]}]}, "state": state})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
        state = reply['result']['state']
 
        a_record = {"expression": "record",
                      "data": {"unit": "()",
                             "fifteen": {"expression": "bits",
                                           "encoding": "hex",
                                           "width": 4,
                                           "data": "f"}}}
 
        uid = c.send_command("evaluate expression", {"state": state, "expression": a_record})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {'expression': 'record',
               'data': {'fifteen':
                             {'data': 'f',
                             'width': 4,
                             'expression': 'bits',
                             'encoding': 'hex'},
                             'unit':
                             {'expression': 'unit'}}})
        state = reply['result']['state']

        uid = c.send_command("evaluate expression",
                             {"state": state,
                             "expression": {"expression": "sequence",
                                                  "data": [a_record, a_record]}})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {'expression': 'sequence',
               'data': [{'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'},
                             {'data': {'fifteen': {'data': 'f', 'width': 4, 'expression': 'bits', 'encoding': 'hex'},
                                    'unit': {'expression': 'unit'}},
                             'expression': 'record'}]})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression",
                             {"state": state,
                             "expression": {"expression": "integer modulo",
                                            "integer": 14,
                                            "modulus": 42}})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {"expression": "integer modulo",
               "integer": 14,
               "modulus": 42})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression",
                             {"state": state,
                             "expression": "m `{a=60}"})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'],
               {"expression": "integer modulo",
               "integer": 42,
               "modulus": 60})
        state = reply['result']['state']
 
 
        uid = c.send_command("evaluate expression", {"state": state, "expression": "two"})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'], {'data': '0002', 'width': 15, 'expression': 'bits', 'encoding': 'hex'})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression", {"state": state, "expression": "three"})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'], {'data': '0003', 'width': 16, 'expression': 'bits', 'encoding': 'hex'})
        state = reply['result']['state']
 
        uid = c.send_command("evaluate expression", {"state": state, "expression": "four"})
        reply = c.wait_for_reply_to(uid)
        self.assertIn('result', reply)
        self.assertIn('answer', reply['result'])
        self.assertIn('value', reply['result']['answer'])
        self.assertEqual(reply['result']['answer']['value'], {'data': '00004', 'width': 17, 'expression': 'bits', 'encoding': 'hex'})
        state = reply['result']['state']

        state = do_test_options(self, c, state, dict())
        state = do_test_options(self, c, state, {"call stacks": True})
        state = do_test_options(self, c, state, {"call stacks": False})
        state = do_test_options(self, c, state, {"call stacks": False, "output": dict()})
        state = do_test_options(self, c, state, {"call stacks": False, "output": {"ASCII": True}})
        state = do_test_options(self, c, state, {"call stacks": False, "output": {"base": 16}})
        state = do_test_options(self, c, state, {"call stacks": False, "output": {"prefix of infinite lengths": 3}})

        # These test both the type instantiation form and the serialization/deserialization of the types involved
        state = do_test_instantiation(self, c, state, {"type": "Integer"})
        state = do_test_instantiation(self, c, state, {"type": "record",
                             "fields": {'a': {'type': 'Integer'},
                                           'b': {'type': 'sequence', 'length': {'type': 'inf'}, 'contents': {'type': 'unit'}}}})
        state = do_test_instantiation(self, c, state, {'type': 'sequence',
                             'length': {'type': 'number', 'value': 42},
                             'contents': {'type': 'Rational'}})
        state = do_test_instantiation(self, c, state, {'type': 'bitvector',
                             'width': {'type': 'number', 'value': 432}})
        state = do_test_instantiation(self, c, state, {'type': 'variable',
                             'name': 'Word8'},
                             {'type': 'bitvector',
                             'width': {'type': 'number', 'value': 8}})
        state = do_test_instantiation(self, c, state, {'type': 'variable',
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

#         if which("cryptol-remote-api"):
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
