"""Cryptol bindings from Python. Use :py:func:`cryptol.connect` to start a new connection."""

from __future__ import annotations

import base64
import os
import types
import sys
from distutils.spawn import find_executable
from typing import Any, Dict, Iterable, List, NoReturn, Optional, Union, Callable
from mypy_extensions import TypedDict

import argo_client.interaction as argo
from argo_client.interaction import HasProtocolState
from argo_client.connection import DynamicSocketProcess, ServerConnection, ServerProcess, StdIOProcess, HttpProcess
from . import cryptoltypes
from . import solver
from .bitvector import BV


__all__ = ['cryptoltypes', 'solver']



# Current status:
#  It can currently launch a server, given a suitable command line as an argument. Try this:
#  >>> c = CryptolConnection("cabal -v0 run cryptol-remote-api")
#  >>> f = c.load_file(FILE)
#  >>> f.result()
#



def extend_hex(string : str) -> str:
    if len(string) % 2 == 1:
        return '0' + string
    else:
        return string

def fail_with(x : Exception) -> NoReturn:
    "Raise an exception. This is valid in expression positions."
    raise x



def from_cryptol_arg(val : Any) -> Any:
    """Return the canonical Python value for a Cryptol JSON value."""
    if isinstance(val, bool):
        return val
    elif isinstance(val, int):
        return val
    elif 'expression' in val.keys():
        tag = val['expression']
        if tag == 'unit':
            return ()
        elif tag == 'tuple':
            return tuple(from_cryptol_arg(x) for x in val['data'])
        elif tag == 'record':
            return {k : from_cryptol_arg(val[k]) for k in val['data']}
        elif tag == 'sequence':
            return [from_cryptol_arg(v) for v in val['data']]
        elif tag == 'bits':
            enc = val['encoding']
            size = val['width']
            if enc == 'base64':
                n = int.from_bytes(
                        base64.b64decode(val['data'].encode('ascii')),
                        byteorder='big')
            elif enc == 'hex':
                n = int.from_bytes(
                    bytes.fromhex(extend_hex(val['data'])),
                    byteorder='big')
            else:
                raise ValueError("Unknown encoding " + str(enc))
            return BV(size, n)
        else:
            raise ValueError("Unknown expression tag " + tag)
    else:
        raise TypeError("Unsupported value " + str(val))



class CryptolChangeDirectory(argo.Command):
    def __init__(self, connection : HasProtocolState, new_directory : str) -> None:
        super(CryptolChangeDirectory, self).__init__(
            'change directory',
            {'directory': new_directory},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return res

class CryptolLoadModule(argo.Command):
    def __init__(self, connection : HasProtocolState, mod_name : str) -> None:
        super(CryptolLoadModule, self).__init__('load module', {'module name': mod_name}, connection)

    def process_result(self, res : Any) -> Any:
        return res

class CryptolLoadFile(argo.Command):
    def __init__(self, connection : HasProtocolState, filename : str) -> None:
        super(CryptolLoadFile, self).__init__('load file', {'file': filename}, connection)

    def process_result(self, res : Any) -> Any:
        return res


class CryptolEvalExpr(argo.Command):
    def __init__(self, connection : HasProtocolState, expr : Any) -> None:
        super(CryptolEvalExpr, self).__init__(
            'evaluate expression',
            {'expression': expr},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return res

class CryptolCall(argo.Command):
    def __init__(self, connection : HasProtocolState, fun : str, args : List[Any]) -> None:
        super(CryptolCall, self).__init__(
            'call',
            {'function': fun, 'arguments': args},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return from_cryptol_arg(res['value'])

class CryptolCheckType(argo.Command):
    def __init__(self, connection : HasProtocolState, expr : Any) -> None:
        super(CryptolCheckType, self).__init__(
            'check type',
            {'expression': expr},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return res['type schema']

class CryptolProveSat(argo.Command):
    def __init__(self, connection : HasProtocolState, qtype : str, expr : Any, solver : solver.Solver, count : Optional[int]) -> None:
        super(CryptolProveSat, self).__init__(
            'prove or satisfy',
            {'query type': qtype,
             'expression': expr,
             'prover': solver,
             'result count': 'all' if count is None else count},
            connection
        )
        self.qtype = qtype

    def process_result(self, res : Any) -> Any:
        if res['result'] == 'unsatisfiable':
            if self.qtype == 'sat':
                return False
            elif self.qtype == 'prove':
                return True
            else:
                raise ValueError("Unknown prove/sat query type: " + self.qtype)
        elif res['result'] == 'invalid':
            return [from_cryptol_arg(arg['expr'])
                    for arg in res['counterexample']]
        elif res['result'] == 'satisfied':
            return [from_cryptol_arg(arg['expr'])
                    for m in res['models']
                    for arg in m]
        else:
            raise ValueError("Unknown sat result " + str(res))

class CryptolProve(CryptolProveSat):
    def __init__(self, connection : HasProtocolState, expr : Any, solver : solver.Solver) -> None:
        super(CryptolProve, self).__init__(connection, 'prove', expr, solver, 1)

class CryptolSat(CryptolProveSat):
    def __init__(self, connection : HasProtocolState, expr : Any, solver : solver.Solver, count : int) -> None:
        super(CryptolSat, self).__init__(connection, 'sat', expr, solver, count)

class CryptolNames(argo.Command):
    def __init__(self, connection : HasProtocolState) -> None:
        super(CryptolNames, self).__init__('visible names', {}, connection)

    def process_result(self, res : Any) -> Any:
        return res

class CryptolFocusedModule(argo.Command):
    def __init__(self, connection : HasProtocolState) -> None:
        super(CryptolFocusedModule, self).__init__(
            'focused module',
            {},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return res

class CryptolReset(argo.Notification):
    def __init__(self, connection : HasProtocolState) -> None:
        super(CryptolReset, self).__init__(
            'clear state',
            {'state to clear': connection.protocol_state()},
            connection
        )

class CryptolResetServer(argo.Notification):
    def __init__(self, connection : HasProtocolState) -> None:
        super(CryptolResetServer, self).__init__(
            'clear all states',
            {},
            connection
        )

def connect(command : Optional[str]=None,
            *,
            cryptol_path : Optional[str] = None,
            url : Optional[str] = None,
            reset_server : bool = False) -> CryptolConnection:
    """
    Connect to a (possibly new) Cryptol server process.

    :param command: A command to launch a new Cryptol server in socket mode (if provided).

    :param cryptol_path: A replacement for the contents of
      the ``CRYPTOLPATH`` environment variable (if provided).

    :param url: A URL at which to connect to an already running Cryptol 
    HTTP server.

    :param reset_server: If ``True``, the server that is connected to will be
    reset. (This ensures any states from previous server usages have been
    cleared.)


    If no ``command`` or ``url`` parameters are provided, the following are attempted in order:

    1. If the environment variable ``CRYPTOL_SERVER`` is set and referse to an executable,
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    2. If the environment variable ``CRYPTOL_SERVER_URL`` is set, it is assumed to be
    the URL for a running Cryptol server in ``http`` mode and will be connected to.

    3. If an executable ``cryptol-remote-api`` is available on the ``PATH``
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    """
    c = None
    if command is not None:
        if url is not None:
            raise ValueError("A Cryptol server URL cannot be specified with a command currently.")
        c = CryptolConnection(command, cryptol_path)
    elif url is not None:
        c = CryptolConnection(ServerConnection(HttpProcess(url)), cryptol_path)
    elif (command := os.getenv('CRYPTOL_SERVER')) is not None and (command := find_executable(command)) is not None:
        c = CryptolConnection(command+" socket", cryptol_path=cryptol_path)
    elif (url := os.getenv('CRYPTOL_SERVER_URL')) is not None:
        c = CryptolConnection(ServerConnection(HttpProcess(url)), cryptol_path)
    elif (command := find_executable('cryptol-remote-api')) is not None:
        c = CryptolConnection(command+" socket", cryptol_path=cryptol_path)
    else:
        raise ValueError(
            """cryptol.connect requires one of the following:",
               1) a command to launch a cryptol server is the first positional argument,
               2) a URL to connect to a running cryptol server is provided via the `url` keyword argument,
               3) the environment variable `CRYPTOL_SERVER` must refer to a valid server executable, or
               4) the environment variable `CRYPTOL_SERVER_URL` must refer to the URL of a running cryptol server.""")
    if reset_server:
        CryptolResetServer(c)
    return c


def connect_stdio(command : str, cryptol_path : Optional[str] = None) -> CryptolConnection:
    """Start a new connection to a new Cryptol server process.

    :param command: The command to launch the Cryptol server.

    :param cryptol_path: An optional replacement for the contents of
      the ``CRYPTOLPATH`` environment variable.

    """
    conn = CryptolStdIOProcess(command, cryptol_path=cryptol_path)

    return CryptolConnection(conn)


class CryptolConnection:
    """Instances of ``CryptolConnection`` represent a particular point of
    time in an interaction with Cryptol. Issuing a command through a
    ``CryptolConnection`` causes it to change its state into one in
    which the command has been carried out.

    ``CryptolConnection`` is in the middle of the abstraction
    hierarchy. It relieves users from thinking about explicitly
    encoding state and protocol messages, but it provides a
    non-blocking interface in which answers from Cryptol must be
    explicitly requested. Note that blocking may occur in the case of
    sequential state dependencies between commands.
    """
    most_recent_result : Optional[argo.Interaction]
    proc: ServerProcess

    def __init__(self,
                command_or_connection : Union[str, ServerConnection, ServerProcess], 
                cryptol_path : Optional[str] = None) -> None:
        self.most_recent_result = None
        if isinstance(command_or_connection, ServerProcess):
            self.proc = command_or_connection
            self.server_connection = ServerConnection(self.proc)
        elif isinstance(command_or_connection, str):
            self.proc = CryptolDynamicSocketProcess(command_or_connection, cryptol_path=cryptol_path)
            self.server_connection = ServerConnection(self.proc)
        else:
            self.server_connection = command_or_connection

    # Currently disabled in (overly?) conservative effort to not accidentally
    # duplicate and share mutable state.

    # def snapshot(self) -> CryptolConnection:
    #     """Create a lightweight snapshot of this connection. The snapshot
    #     shares the underlying server process, but can have different
    #     application state.
    #     """
    #     copy = CryptolConnection(self.server_connection)
    #     copy.most_recent_result = self.most_recent_result
    #     return copy

    def protocol_state(self) -> Any:
        if self.most_recent_result is None:
            return None
        else:
            return self.most_recent_result.state()

    # Protocol messages
    def change_directory(self, new_directory : str) -> argo.Command:
        """Change the working directory of the Cryptol process."""
        self.most_recent_result = CryptolChangeDirectory(self, new_directory)
        return self.most_recent_result

    def load_file(self, filename : str) -> argo.Command:
        """Load a filename as a Cryptol module, like ``:load`` at the Cryptol
        REPL.
        """
        self.most_recent_result = CryptolLoadFile(self, filename)
        return self.most_recent_result

    def load_module(self, module_name : str) -> argo.Command:
        """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
        self.most_recent_result = CryptolLoadModule(self, module_name)
        return self.most_recent_result

    def eval(self, expression : Any) -> argo.Command:
        """Evaluate a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing
        for their JSON equivalents.
        """
        self.most_recent_result = CryptolEvalExpr(self, expression)
        return self.most_recent_result

    def evaluate_expression(self, expression : Any) -> argo.Command:
        """Synonym for member method ``eval``.
        """
        return self.eval(expression)

    def call(self, fun : str, *args : List[Any]) -> argo.Command:
        encoded_args = [cryptoltypes.CryptolType().from_python(a) for a in args]
        self.most_recent_result = CryptolCall(self, fun, encoded_args)
        return self.most_recent_result

    def check_type(self, code : Any) -> argo.Command:
        """Check the type of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents.
        """
        self.most_recent_result = CryptolCheckType(self, code)
        return self.most_recent_result

    def sat(self, expr : Any, solver : solver.Solver = solver.Z3, count : int = 1) -> argo.Command:
        """Check the satisfiability of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`, and return up to
        `count` solutions.
        """
        self.most_recent_result = CryptolSat(self, expr, solver, count)
        return self.most_recent_result

    def prove(self, expr : Any, solver : solver.Solver = solver.Z3) -> argo.Command:
        """Check the validity of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`.
        """
        self.most_recent_result = CryptolProve(self, expr, solver)
        return self.most_recent_result

    def names(self) -> argo.Command:
        """Discover the list of names currently in scope in the current context."""
        self.most_recent_result = CryptolNames(self)
        return self.most_recent_result

    def focused_module(self) -> argo.Command:
        """Return the name of the currently-focused module."""
        self.most_recent_result = CryptolFocusedModule(self)
        return self.most_recent_result

    def reset(self) -> None:
        """Resets the connection, causing its unique state on the server to be freed (if applicable).
        
        After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
        CryptolReset(self)
        self.most_recent_result = None

    def reset_server(self) -> None:
        """Resets the Cryptol server, clearing all states."""
        CryptolResetServer(self)
        self.most_recent_result = None

    def __del__(self) -> None:
        # when being deleted, ensure we don't have a lingering state on the server
        if self.most_recent_result is not None:
            try:
                CryptolReset(self)
            except Exception:
                pass

class CryptolDynamicSocketProcess(DynamicSocketProcess):

    def __init__(self, command: str, *,
                 persist: bool=False,
                 cryptol_path: Optional[str]=None):

        environment = os.environ.copy()
        if cryptol_path is not None:
            environment["CRYPTOLPATH"] = str(cryptol_path)

        super().__init__(command, persist=persist, environment=environment)

class CryptolStdIOProcess(StdIOProcess):

    def __init__(self, command: str, *,
                 cryptol_path: Optional[str]=None):

        environment = os.environ.copy()
        if cryptol_path is not None:
            environment["CRYPTOLPATH"] = str(cryptol_path)

        super().__init__(command, environment=environment)


def cry(string : str) -> cryptoltypes.CryptolCode:
    return cryptoltypes.CryptolLiteral(string)

# The below code relies on `connection.snapshot()` which duplicates
# a connection and points to the same underlying server state. We
# should come back to this and reevaluate if/how to do this, given
# that some of our servers have varying degrees of mutable state.

# class CryptolFunctionHandle:
#     def __init__(self,
#                  connection : CryptolConnection,
#                  name : str,
#                  ty : Any,
#                  schema : Any,
#                  docs : Optional[str] = None) -> None:
#         self.connection = connection.snapshot()
#         self.name = name
#         self.ty = ty
#         self.schema = schema
#         self.docs = docs

#         self.__doc__ = "Cryptol type: " + ty
#         if self.docs is not None and self.__doc__ is not None:
#             self.__doc__ += "\n" + self.docs

#     def __call__(self, *args : List[Any]) -> Any:
#         current_type = self.schema
#         remaining_args = args
#         arg_types = cryptoltypes.argument_types(current_type)
#         Call = TypedDict('Call', {'expression': str, 'function': str, 'arguments': List[Any]})
#         current_expr : Union[str, Call]
#         current_expr = self.name
#         found_args = []
#         while len(arg_types) > 0 and len(remaining_args) > 0:
#             found_args.append(arg_types[0].from_python(remaining_args[0]))
#             current_expr = {'expression': 'call', 'function': self.name, 'arguments': found_args}
#             ty = self.connection.check_type(current_expr).result()
#             current_type = cryptoltypes.to_schema(ty)
#             arg_types = cryptoltypes.argument_types(current_type)
#             remaining_args = remaining_args[1:]
#         return from_cryptol_arg(self.connection.evaluate_expression(current_expr).result()['value'])

# class CryptolModule(types.ModuleType):
#     def __init__(self, connection : CryptolConnection) -> None:
#         self.connection = connection.snapshot()
#         name = connection.focused_module().result()
#         if name["module"] is None:
#             raise ValueError("Provided connection is not in a module")
#         super(CryptolModule, self).__init__(name["module"])

#         for x in self.connection.names().result():
#             if 'documentation' in x:
#                 setattr(self, x['name'],
#                         CryptolFunctionHandle(self.connection,
#                                               x['name'],
#                                               x['type string'],
#                                               cryptoltypes.to_schema(x['type']),
#                                               x['documentation']))
#             else:
#                 setattr(self, x['name'],
#                         CryptolFunctionHandle(self.connection,
#                                               x['name'],
#                                               x['type string'],
#                                               cryptoltypes.to_schema(x['type'])))


# def add_cryptol_module(name : str, connection : CryptolConnection) -> None:
#     """Given a name for a Python module and a Cryptol connection,
#     establish a Python module with the given name in which all the
#     Cryptol names are in scope as Python proxy objects.
#     """
#     sys.modules[name] = CryptolModule(connection)

# class CryptolContext:
#     _defined : Dict[str, CryptolFunctionHandle]

#     def __init__(self, connection : CryptolConnection) -> None:
#         self.connection = connection.snapshot()
#         self._defined = {}
#         for x in self.connection.names().result():
#             if 'documentation' in x:
#                 self._defined[x['name']] = \
#                     CryptolFunctionHandle(self.connection,
#                                           x['name'],
#                                           x['type string'],
#                                           cryptoltypes.to_schema(x['type']),
#                                           x['documentation'])
#             else:
#                 self._defined[x['name']] = \
#                     CryptolFunctionHandle(self.connection,
#                                           x['name'],
#                                           x['type string'],
#                                           cryptoltypes.to_schema(x['type']))

#     def __dir__(self) -> Iterable[str]:
#         return self._defined.keys()

#     def __getattr__(self, name : str) -> Any:
#         if name in self._defined:
#             return self._defined[name]
#         else:
#             raise AttributeError()
