
from __future__ import annotations

import os
from distutils.spawn import find_executable
from typing import Any, List, Optional, Union
from typing_extensions import Literal

import argo_client.interaction as argo
from argo_client.connection import DynamicSocketProcess, ServerConnection, ServerProcess, StdIOProcess, HttpProcess
from . import cryptoltypes
from . import solver
from .commands import * 


def connect(command : Optional[str]=None,
            *,
            cryptol_path : Optional[str] = None,
            url : Optional[str] = None,
            reset_server : bool = False,
            verify : Union[bool, str] = True) -> CryptolConnection:
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

    :param verify: Determines whether a secure HTTP connection should verify the SSL certificates.
                   Corresponds to the ``verify`` keyword parameter on ``requests.post``. N.B.,
                   only has an affect when ``connect`` is called with a ``url`` parameter
                   or when the ``CRYPTOL_SERVER_URL`` environment variable is set.


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
    # User-passed url?
    if c is None and url is not None:
        c = CryptolConnection(ServerConnection(HttpProcess(url, verify=verify)), cryptol_path)
    # Check `CRYPTOL_SERVER` env var if no connection identified yet
    if c is None:
        command = os.getenv('CRYPTOL_SERVER')
        if command is not None:
            command = find_executable(command)
            if command is not None:
                c = CryptolConnection(command+" socket", cryptol_path=cryptol_path)
    # Check `CRYPTOL_SERVER_URL` env var if no connection identified yet
    if c is None:
        url = os.getenv('CRYPTOL_SERVER_URL')
        if url is not None:
            c = CryptolConnection(ServerConnection(HttpProcess(url,verify=verify)), cryptol_path)
    # Check if `cryptol-remote-api` is in the PATH if no connection identified yet
    if c is None:
        command = find_executable('cryptol-remote-api')
        if command is not None:
            c = CryptolConnection(command+" socket", cryptol_path=cryptol_path)
    # Raise an error if still no connection identified yet
    if c is not None:
        if reset_server:
            CryptolResetServer(c)
        return c
    else:
        raise ValueError(
            """cryptol.connect requires one of the following:",
               1) a command to launch a cryptol server is the first positional argument,
               2) a URL to connect to a running cryptol server is provided via the `url` keyword argument,
               3) the environment variable `CRYPTOL_SERVER` must refer to a valid server executable, or
               4) the environment variable `CRYPTOL_SERVER_URL` must refer to the URL of a running cryptol server.""")



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

    def extend_search_path(self, *dir : str) -> argo.Command:
        """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
        self.most_recent_result = CryptolExtendSearchPath(self, list(dir))
        return self.most_recent_result

    def call(self, fun : str, *args : List[Any]) -> argo.Command:
        encoded_args = [cryptoltypes.CryptolType().from_python(a) for a in args]
        self.most_recent_result = CryptolCall(self, fun, encoded_args)
        return self.most_recent_result

    def check(self, expr : Any, *, num_tests : Union[Literal['all'], int, None] = None) -> argo.Command:
        """Tests the validity of a Cryptol expression with random inputs. The expression must be a function with
        return type ``Bit``.

        If ``num_tests`` is ``"all"`` then the expression is tested exhaustively (i.e., against all possible inputs).

        If ``num_tests`` is omitted, Cryptol defaults to running 100 tests.
        """
        if num_tests == "all" or isinstance(num_tests, int) or num_tests is None:
            self.most_recent_result = CryptolCheck(self, expr, num_tests)
            return self.most_recent_result
        else:
            raise ValueError('``num_tests`` must be an integer, ``None``, or the string literall ``"all"``')


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

    def safe(self, expr : Any, solver : solver.Solver = solver.Z3) -> argo.Command:
        """Check via an external SMT solver that the given term is safe for all inputs,
        which means it cannot encounter a run-time error.
        """
        self.most_recent_result = CryptolSafe(self, expr, solver)
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
