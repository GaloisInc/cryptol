import os
from pathlib import Path
import signal
import subprocess
import distutils.spawn
import time
import unittest

import argo_client.connection as argo
import cryptol
from cryptol import CryptolConnection, CryptolContext, cry

dir_path = Path(os.path.dirname(os.path.realpath(__file__)))

cryptol_path = dir_path.joinpath('test-data')


def exe_exists(name : str) -> bool:
    return distutils.spawn.find_executable(name) is not None

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

class GenericLowLevelCryptolApiTests():
    # to be implemented by classes extending this one
    def get_connection(self): pass

    def test_low_level_api(self):
        c = self.get_connection()
        id_1 = c.send_command("load module", {"module name": "M", "state": None})
        reply_1 = c.wait_for_reply_to(id_1)
        assert('result' in reply_1)
        assert('state' in reply_1['result'])
        assert('answer' in reply_1['result'])
        state_1 = reply_1['result']['state']
 
        id_2 = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"f","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state_1})
        reply_2 = c.wait_for_reply_to(id_2)
        assert('result' in reply_2)
        assert('answer' in reply_2['result'])
        assert('value' in reply_2['result']['answer'])
        assert(reply_2['result']['answer']['value'] ==
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
 
        id_3 = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"g","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": state_1})
        reply_3 = c.wait_for_reply_to(id_3)
        assert('result' in reply_3)
        assert('answer' in reply_3['result'])
        assert('value' in reply_3['result']['answer'])
        assert(reply_3['result']['answer']['value'] ==
               {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                             {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
               'expression': 'sequence'})
 
        id_4 = c.send_query("evaluate expression", {"expression":{"expression":"call","function":"h","arguments":[{"expression":"sequence","data":[{"expression":"bits","encoding":"hex","data":"ff","width":8},{"expression":"bits","encoding":"hex","data":"ff","width":8}]}]}, "state": state_1})
        reply_4 = c.wait_for_reply_to(id_4)
        assert('result' in reply_4)
        assert('answer' in reply_4['result'])
        assert('value' in reply_4['result']['answer'])
        assert(reply_4['result']['answer']['value'] ==
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
        assert('result' in reply_5)
        assert('answer' in reply_5['result'])
        assert('value' in reply_5['result']['answer'])
        assert(reply_5['result']['answer']['value'] ==
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
        assert('result' in reply_6)
        assert('answer' in reply_6['result'])
        assert('value' in reply_6['result']['answer'])
        assert(reply_6['result']['answer']['value'] ==
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
        assert('result' in reply_7)
        assert('answer' in reply_7['result'])
        assert('value' in reply_7['result']['answer'])
        assert(reply_7['result']['answer']['value'] ==
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
        assert('result' in reply_8)
        assert('answer' in reply_8['result'])
        assert('value' in reply_8['result']['answer'])
        assert(reply_8['result']['answer']['value'] ==
               {"expression": "integer modulo",
               "integer": 14,
               "modulus": 42})
 
        id_9 = c.send_query("evaluate expression",
                             {"state": state_1,
                             "expression": "m `{a=60}"})
        reply_9 = c.wait_for_reply_to(id_9)
        assert('result' in reply_9)
        assert('answer' in reply_9['result'])
        assert('value' in reply_9['result']['answer'])
        assert(reply_9['result']['answer']['value'] ==
               {"expression": "integer modulo",
               "integer": 42,
               "modulus": 60})
 
 
        id_10 = c.send_query("evaluate expression", {"state": state_1, "expression": "two"})
        reply_10 = c.wait_for_reply_to(id_10)
        assert('result' in reply_10)
        assert('answer' in reply_10['result'])
        assert('value' in reply_10['result']['answer'])
        assert(reply_10['result']['answer']['value'] == {'data': '0002', 'width': 15, 'expression': 'bits', 'encoding': 'hex'})
 
        id_11 = c.send_query("evaluate expression", {"state": state_1, "expression": "three"})
        reply_11 = c.wait_for_reply_to(id_11)
        assert('result' in reply_11)
        assert('answer' in reply_11['result'])
        assert('value' in reply_11['result']['answer'])
        assert(reply_11['result']['answer']['value'] == {'data': '0003', 'width': 16, 'expression': 'bits', 'encoding': 'hex'})
 
        id_12 = c.send_query("evaluate expression", {"state": state_1, "expression": "four"})
        reply_12 = c.wait_for_reply_to(id_12)
        assert('result' in reply_12)
        assert('answer' in reply_12['result'])
        assert('value' in reply_12['result']['answer'])
        assert(reply_12['result']['answer']['value'] == {'data': '00004', 'width': 17, 'expression': 'bits', 'encoding': 'hex'})

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


class DynamicSocketLowLevelCryptolApiTests(GenericLowLevelCryptolApiTests, unittest.TestCase):
    c = None

    @classmethod
    def setUpClass(self):
        if exe_exists("cryptol-remote-api"):
            self.c = argo.ServerConnection(cryptol.CryptolDynamicSocketProcess(
                "cryptol-remote-api socket",
                cryptol_path=cryptol_path))
        else:
            self.c = argo.ServerConnection(cryptol.CryptolDynamicSocketProcess(
                "cabal run --verbose=0 exe:cryptol-remote-api -- socket",
                cryptol_path=cryptol_path))

    # to be implemented by classes extending this one
    def get_connection(self):
        return self.c


class StdIOLowLevelCryptolApiTests(GenericLowLevelCryptolApiTests, unittest.TestCase):
    c = None
    @classmethod
    def setUpClass(self):
        if exe_exists("cryptol-remote-api"):
            self.c = argo.ServerConnection(cryptol.CryptolStdIOProcess(
                "cryptol-remote-api stdio",
                cryptol_path=cryptol_path))
        else:
            self.c = argo.ServerConnection(cryptol.CryptolStdIOProcess(
                "cabal run --verbose=0 exe:cryptol-remote-api -- stdio",
                cryptol_path=cryptol_path))

    # to be implemented by classes extending this one
    def get_connection(self):
        return self.c

class RemoteSockeLowLevelCryptolApiTests(GenericLowLevelCryptolApiTests, unittest.TestCase):
    p = None

    @classmethod
    def setUpClass(self):
        env = os.environ.copy()
        env['CRYPTOLPATH'] = cryptol_path

        if exe_exists("cryptol-remote-api"):
            p = subprocess.Popen(
                ["cryptol-remote-api", "socket", "--port", "50005"],
                stdout=subprocess.DEVNULL,
                stdin=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
                env=env)
        else:
            p = subprocess.Popen(
                ["cabal", "run", "exe:cryptol-remote-api", "--verbose=0", "--",  "socket", "--port", "50005"],
                stdout=subprocess.DEVNULL,
                stdin=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
                env=env)
        time.sleep(5)
        assert(p is not None)
        poll_result = p.poll()
        if poll_result is not None:
            print(poll_result)
            print(p.stdout.read())
            print(p.stderr.read())
        assert(poll_result is None)
        self.p = p

        self.c = argo.ServerConnection(argo.RemoteSocketProcess('localhost', 50005, ipv6=True))

    @classmethod
    def tearDownClass(self):
        os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
        super().tearDownClass()

    # to be implemented by classes extending this one
    def get_connection(self):
        return self.c

