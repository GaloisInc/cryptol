import os
from pathlib import Path
import signal
import subprocess
import time
import unittest
from shutil import which
import cryptol
from cryptol.bitvector import BV


class CryptolEvalServerTests(unittest.TestCase):
    # Connection to cryptol
    c = None

    @classmethod
    def setUpClass(self):
        dir_path = Path(os.path.dirname(os.path.realpath(__file__)), "test-files")
        server = os.getenv('CRYPTOL_SERVER')
        if server:
            self.c = cryptol.connect(f'{server} socket --module M', cryptol_path=dir_path)
        else:
            raise ValueError('CRYPTOL_SERVER environment variable not set (eval server tests currently only work with a local executable)')


    def test_evaluation(self):
        if self.c:
            c = self.c
            res = c.call('f', BV(size=8,value=0xff)).result()
            self.assertEqual(res, [BV(size=8,value=0xff), BV(size=8,value=0xff)])


    # more thorough testing of backend functionality found in standard server's tests
    def test_sat(self):
        c = self.c
        # test a single sat model can be returned
        rootsOf9 = c.sat('isSqrtOf9').result()
        self.assertEqual(len(rootsOf9), 1)
        self.assertTrue(int(rootsOf9[0]) ** 2 % 256, 9)

    # more thorough testing of backend functionality found in standard server's tests
    def test_check(self):
        c = self.c
        res = c.check("\\x -> x==(x:[8])").result()
        self.assertTrue(res.success)

    # def test_disallowed_ops(self):
    #     pass # TODO/FIXME


class HttpMultiConnectionTests(unittest.TestCase):
    # Connection to server
    c = None
    # Python initiated process running the server (if any)
    p = None
    # url of HTTP server
    url = None

    @classmethod
    def setUpClass(self):
        dir_path = Path(os.path.dirname(os.path.realpath(__file__)), "test-files")
        server = os.getenv('CRYPTOL_SERVER')
        if server is not None:
            server = which(server)
        if server is None:
            server = which('cryptol-eval-server')
        if server is not None:
            new_env = os.environ.copy()
            new_env["CRYPTOLPATH"] = str(dir_path)
            self.p = subprocess.Popen(
                [server, "http", "/", "--port", "8081", "--module", "M"],
                stdout=subprocess.PIPE,
                stdin=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                start_new_session=True,
                env=new_env)
            time.sleep(5)
            assert(self.p is not None)
            poll_result = self.p.poll()
            if poll_result is not None:
                print(poll_result)
                print(self.p.stdout.read())
                print(self.p.stderr.read())
            assert(poll_result is None)
            self.url = "http://localhost:8081/"
        elif os.getenv('CRYPTOL_SERVER_URL') is not None:
            raise ValueError('CRYPTOL_SERVER_URL environment variable is set but the eval server tests currently only work with a local executable')
        else:
            raise RuntimeError("NO CRYPTOL EVAL SERVER FOUND")

    @classmethod
    def tearDownClass(self):
        if self.p is not None:
            os.killpg(os.getpgid(self.p.pid), signal.SIGKILL)
        super().tearDownClass()

    def test_reset_with_many_usages_many_connections(self):
        for i in range(0,100):
            time.sleep(.05)
            c = cryptol.connect(url=self.url)
            res = c.call('f', BV(size=8,value=0xff)).result()
            self.assertEqual(res, [BV(size=8,value=0xff), BV(size=8,value=0xff)])
            c.reset()

    def test_server_with_many_usages_many_connections(self):
        for i in range(0,100):
            time.sleep(.05)
            c = cryptol.connect(url=self.url)
            res = c.call('f', BV(size=8,value=0xff)).result()
            self.assertEqual(res, [BV(size=8,value=0xff), BV(size=8,value=0xff)])

if __name__ == "__main__":
    unittest.main()
