import os
from pathlib import Path
import signal
import subprocess
import time

import argo.connection as argo
import cryptol

dir_path = Path(os.path.dirname(os.path.realpath(__file__)))

cryptol_path = dir_path.joinpath('test-data')


env = os.environ.copy()
env['CRYPTOLPATH'] = cryptol_path

p = subprocess.Popen(
    ["cabal", "v2-exec", "cryptol-eval-server", "--verbose=0", "--", "http", "/", "--port", "50005", "--module", "M"],
    stdout=subprocess.PIPE,
    stdin=subprocess.DEVNULL,
    stderr=subprocess.PIPE,
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

c = argo.ServerConnection(argo.HttpProcess('http://localhost:50005/'))


mid = c.send_query("evaluate expression", {"expression": {"expression":"call","function":"f","arguments":[{"expression":"bits","encoding":"hex","data":"ff","width":8}]}, "state": None})
reply = c.wait_for_reply_to(mid)
assert('result' in reply)
assert('answer' in reply['result'])
assert('value' in reply['result']['answer'])
assert(reply['result']['answer']['value'] ==
       {'data': [{'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'},
                 {'data': 'ff', 'width': 8, 'expression': 'bits', 'encoding': 'hex'}],
        'expression': 'sequence'})

os.killpg(os.getpgid(p.pid), signal.SIGKILL)
