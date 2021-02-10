import os
from pathlib import Path
import signal
import subprocess
import time
import unittest

import argo_client.connection as argo



class CryptolEvalServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None
    # process running the server
    p = None

    @classmethod
    def setUpClass(self):
        dir_path = Path(os.path.dirname(os.path.realpath(__file__)))
        cryptol_path = dir_path.joinpath('test-data')
        env = os.environ.copy()
        env['CRYPTOLPATH'] = cryptol_path

        p = subprocess.Popen(
            ["cabal", "run", "cryptol-eval-server", "--verbose=0", "--", "http", "/", "--port", "50005", "--module", "M"],
            stdout=subprocess.PIPE,
            stdin=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            start_new_session=True,
            env=env)
        time.sleep(3)
        assert(p is not None)
        poll_result = p.poll()
        if poll_result is not None:
            print(poll_result)
            print(p.stdout.read())
            print(p.stderr.read())
        assert(poll_result is None)

        self.p = p
        self.c = argo.ServerConnection(argo.HttpProcess('http://localhost:50005/'))


    @classmethod
    def tearDownClass(self):
        os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
        super().tearDownClass()


    @classmethod
    def test_eval_server(self):
        c = self.c
        mid = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"f","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": None})
        reply = c.wait_for_reply_to(mid)
        assert('result' in reply)
        assert('answer' in reply['result'])
        assert('value' in reply['result']['answer'])
        assert(reply['result']['answer']['value'] ==
            {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                        {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
                'expression': 'sequence'})


