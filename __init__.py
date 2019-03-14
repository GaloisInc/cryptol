import base64
import socket
import json


from . import netstring
from . import types

__all__ = ['types']

# Current status:
#  It can currently connect to a server over a socket. Try the following:
#  >>> c = CryptolConnection(PORT)
#  >>> f = c.load_file(FILE)
#  >>> f.result()
#



def extend_hex(string):
    if len(string) % 2 == 1:
        return '0' + string
    else:
        return string

def fail_with(x):
    "Raise an exception. This is valid in expression positions."
    raise x


import re

m = r"\{\{([a-zA-Z0-9]+)\}\}"





def from_cryptol_arg(val):
    if isinstance(val, bool):
        return val
    elif isinstance(val, int):
        return val
    elif 'expression' in val.keys():
        tag = val['expression']
        if tag == 'unit':
            return ()
        elif tag == 'tuple':
            return (from_cryptol_arg(x) for x in val['data'])
        elif tag == 'record':
            return {k : from_cryptol_arg(val[k]) for k in val['data']}
        elif tag == 'sequence':
            return [from_cryptol_arg(v) for v in val['data']]
        elif tag == 'bits':
            enc = val['encoding']
            if enc == 'base64':
                data = base64.b64decode(val['data'].encode('ascii'))
            elif enc == 'hex':
                data = bytes.fromhex(extend_hex(val['data']))
            else:
                raise ValueError("Unknown encoding " + str(enc))
            return data
        else:
            raise ValueError("Unknown expression tag " + tag)
    else:
        raise TypeError("Unsupported value " + str(val))


class CryptolException(Exception):
    pass

class CryptolInteraction():
    def __init__(self, connection):
        self.connection = connection
        self._raw_response = None
        self.init_state = connection.protocol_state()
        self.params['state'] = self.init_state
        self.request_id = connection.send_message(self.method, self.params)

    def raw_result(self):
        if self._raw_response is None:
            self._raw_response = self.connection.wait_for_reply_to(self.request_id)
        return self._raw_response

    def process_result(self, result):
        raise NotImplementedError('process_result')

class CryptolCommand(CryptolInteraction):

    def _result_and_state(self):
        res = self.raw_result()
        if 'error' in res:
            msg = res['error']['message']
            if 'data' in res['error']:
                msg += " " + str(res['error']['data'])
            raise CryptolException(msg)
        elif 'result' in res:
            return (res['result']['answer'], res['result']['state'])

    def state(self):
        return self._result_and_state()[1]

    def result(self):
        return self.process_result(self._result_and_state()[0])

class CryptolChangeDirectory(CryptolCommand):
    def __init__(self, connection, new_directory):
        self.method = 'change directory'
        self.params = {'directory': new_directory}
        super(CryptolChangeDirectory, self).__init__(connection)

    def process_result(self, res):
        return res

class CryptolLoadModule(CryptolCommand):
    def __init__(self, connection, filename):
        self.method = 'load module'
        self.params = {'file': filename}
        super(CryptolLoadModule, self).__init__(connection)

    def process_result(self, res):
        return res

class CryptolQuery(CryptolInteraction):
    def state(self):
        return self.init_state

    def _result(self):
        res = self.raw_result()
        if 'error' in res:
            msg = res['error']['message']
            if 'data' in res['error']:
                msg += " " + str(res['error']['data'])
            raise CryptolException(msg)
        elif 'result' in res:
            return res['result']['answer']

    def result(self):
        return self.process_result(self._result())

class CryptolEvalExpr(CryptolQuery):
    def __init__(self, connection, expr):
        self.method = 'evaluate expression'
        self.params = {'expression': expr}
        super(CryptolEvalExpr, self).__init__(connection)

    def process_result(self, res):
        return res

class CryptolCall(CryptolQuery):
    def __init__(self, connection, fun, args):
        self.method = 'call'
        self.params = {'function': fun, 'arguments': args}
        super(CryptolCall, self).__init__(connection)

    def process_result(self, res):
        return from_cryptol_arg(res['value'])

class CryptolNames(CryptolQuery):
    def __init__(self, connection):
        self.method = 'visible names'
        self.params = {}
        super(CryptolQuery, self).__init__(connection)

    def process_result(self, res):
        return res

# Must be boxed separately to enable sharing of connections
class IDSource:
    def __init__(self):
        self.next_id = 0

    def get(self):
        self.next_id += 1
        return self.next_id

class CryptolConnection(object):
    def __init__(self, port, parent=None):
        self.port = port

        if parent is None:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect(("127.0.0.1", port))
            self.sock.setblocking(False)
            self.buf = bytearray(b'')
            self.replies = {}
            self.ids = IDSource()
            self.most_recent_result = None
        else:
            self.sock = parent.sock
            self.buf = parent.buf
            self.replies = parent.replies
            self.ids = parent.ids
            self.most_recent_result = parent.most_recent_result

    def snapshot(self):
        return CryptolConnection(self.port, parent=self)

    def get_id(self):
        return self.ids.get()

    def buffer_replies(self):
        try:
            arrived = self.sock.recv(4096)
            while arrived != b'':
                self.buf.extend(arrived)
                arrived = self.sock.recv(4096)
            return None
        except BlockingIOError:
            return None

    def get_one_reply(self):
        try:
            (msg, rest) = netstring.decode(self.buf)
            self.buf = rest
            return msg
        except (ValueError, IndexError):
            return None

    def process_replies(self):
        self.buffer_replies()
        r = self.get_one_reply()
        while r is not None:
            the_reply = json.loads(r)
            self.replies[the_reply['id']] = the_reply
            r = self.get_one_reply()

    def send_message(self, method, params):
        request_id = self.get_id()
        msg = {'jsonrpc':'2.0',
               'method': method,
               'id': request_id,
               'params': params}
        msg_string = json.dumps(msg)
        msg_bytes = netstring.encode(msg_string)
        self.sock.send(msg_bytes)
        return request_id

    def wait_for_reply_to(self, request_id):
        self.process_replies()
        while request_id not in self.replies:
            try:
                #self.sock.setblocking(True)
                self.process_replies()
            finally:
                self.sock.setblocking(False)
        return self.replies[request_id]

    def protocol_state(self):
        if self.most_recent_result is None:
            return []
        else:
            return self.most_recent_result.state()

    # Protocol messages
    def change_directory(self, new_directory):
        self.most_recent_result = CryptolChangeDirectory(self, new_directory)
        return self.most_recent_result

    def load_file(self, filename):
        self.most_recent_result = CryptolLoadModule(self, filename)
        return self.most_recent_result

    def evaluate_expression(self, expression):
        self.most_recent_result = CryptolEvalExpr(self, expression)
        return self.most_recent_result

    def call(self, fun, *args):
        encoded_args = [types.CryptolType().from_python(a) for a in args]
        self.most_recent_result = CryptolCall(self, fun, encoded_args)
        return self.most_recent_result

    def names(self):
        self.most_recent_result = CryptolNames(self)
        return self.most_recent_result

class CryptolFunctionHandle:
    def __init__(self, connection, name, ty, schema, docs=None):
        self.connection = connection.snapshot()
        self.name = name
        self.ty = ty
        self.schema = schema
        self.docs = docs

        self.__doc__ = "Cryptol type: " + ty
        if self.docs is not None:
            self.__doc__ += "\n" + self.docs

    def __call__(self, *args):
        return self.connection.call(self.name, *args).result()



class CryptolContext:
    def __init__(self, connection):
        self.connection = connection.snapshot()
        self._defined = {}
        for x in self.connection.names().result():
            if 'documentation' in x:
                self._defined[x['name']] = \
                    CryptolFunctionHandle(self.connection,
                                          x['name'],
                                          x['type string'],
                                          types.to_schema(x['type']),
                                          x['documentation'])
            else:
                self._defined[x['name']] = \
                    CryptolFunctionHandle(self.connection,
                                          x['name'],
                                          x['type string'],
                                          types.to_schema(x['type']))

    def __dir__(self):
        return self._defined.keys()

    def __getattr__(self, name):
        if name in self._defined:
            return self._defined[name]
        else:
            raise AttributeError()
