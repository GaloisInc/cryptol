"""A synchronous, typed interface for the Cryptol bindings"""

from __future__ import annotations

import sys
from typing import cast, Any, Optional, Union, List, Dict, TextIO
from typing_extensions import Literal

from . import solver
from . import connection
from . import cryptoltypes
from .commands import *
from . import CryptolConnection, SmtQueryType


def connect_sync(command : Optional[str]=None,
                 *,
                 cryptol_path : Optional[str] = None,
                 url : Optional[str] = None,
                 reset_server : bool = False,
                 verify : Union[bool, str] = True,
                 log_dest : Optional[TextIO] = None) -> CryptolSyncConnection:
    """
    Connect to a (possibly new) synchronous Cryptol server process.

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

    :param log_dest: A destination to log JSON requests/responses to, e.g. ``log_dest=sys.stderr``
    will print traffic to ``stderr``, ``log_dest=open('foo.log', 'w')`` will log to ``foo.log``,
    etc.

    If no ``command`` or ``url`` parameters are provided, the following are attempted in order:

    1. If the environment variable ``CRYPTOL_SERVER`` is set and referse to an executable,
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    2. If the environment variable ``CRYPTOL_SERVER_URL`` is set, it is assumed to be
    the URL for a running Cryptol server in ``http`` mode and will be connected to.

    3. If an executable ``cryptol-remote-api`` is available on the ``PATH``
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    """
    return CryptolSyncConnection(connection.connect(
        command=command,
        cryptol_path=cryptol_path,
        url=url,
        reset_server=reset_server,
        verify=verify,
        log_dest=log_dest))

def connect_sync_stdio(command : str, cryptol_path : Optional[str] = None) -> CryptolSyncConnection:
    """Start a new synchronous connection to a new Cryptol server process.
    :param command: The command to launch the Cryptol server.
    :param cryptol_path: An optional replacement for the contents of
      the ``CRYPTOLPATH`` environment variable.
    """
    return CryptolSyncConnection(connection.connect_stdio(
        command=command,
        cryptol_path=cryptol_path))


class CryptolSyncConnection:
    """A wrapper of ``CryptolConnection`` with a synchronous, typed interface."""
    connection : CryptolConnection

    def __init__(self, connection : CryptolConnection):
        self.connection = connection

    def load_file(self, filename : str) -> None:
        """Load a filename as a Cryptol module, like ``:load`` at the Cryptol
        REPL.
        """
        self.connection.load_file(filename).result()

    def load_module(self, module_name : str) -> None:
        """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
        self.connection.load_module(module_name).result()

    def extend_search_path(self, *dir : str) -> None:
        """Extend the search path for loading Cryptol modules."""
        self.connection.extend_search_path(*dir).result()

    def eval(self, expression : Any) -> CryptolPython:
        """Evaluate a Cryptol expression, with the result represented
        according to :ref:`cryptol-json-expression`, with Python datatypes
        standing for their JSON equivalents.
        """
        return from_cryptol_arg(self.connection.eval_raw(expression).result())

    def call(self, fun : str, *args : List[Any]) -> CryptolPython:
        """Evaluate a Cryptol functiom by name, with the arguments and the
        result represented according to :ref:`cryptol-json-expression`, with
        Python datatypes standing for their JSON equivalents.
        """
        return from_cryptol_arg(self.connection.call_raw(fun, *args).result())

    def check(self, expr : Any, *, num_tests : Union[Literal['all'], int, None] = None) -> CheckReport:
        """Tests the validity of a Cryptol expression with random inputs. The expression must be a function with
        return type ``Bit``.
        If ``num_tests`` is ``"all"`` then the expression is tested exhaustively (i.e., against all possible inputs).
        If ``num_tests`` is omitted, Cryptol defaults to running 100 tests.
        """
        return to_check_report(self.connection.check_raw(expr, num_tests=num_tests).result())

    def check_type(self, code : Any) -> cryptoltypes.CryptolType:
        """Check the type of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents.
        """
        return cryptoltypes.to_type(self.connection.check_type(code).result()['type'])

    def sat(self, expr : Any, solver : solver.Solver = solver.Z3, count : int = 1) -> SmtQueryResult:
        """Check the satisfiability of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`, and return up to
        `count` solutions.
        """
        return to_smt_query_result(SmtQueryType.SAT, self.connection.sat_raw(expr, solver, count).result())

    def prove(self, expr : Any, solver : solver.Solver = solver.Z3) -> SmtQueryResult:
        """Check the validity of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`.
        """
        return to_smt_query_result(SmtQueryType.PROVE, self.connection.prove_raw(expr, solver).result())

    def safe(self, expr : Any, solver : solver.Solver = solver.Z3) -> SmtQueryResult:
        """Check via an external SMT solver that the given term is safe for all inputs,
        which means it cannot encounter a run-time error.
        """
        return to_smt_query_result(SmtQueryType.SAFE, self.connection.safe_raw(expr, solver).result())

    def names(self) -> List[Dict[str,Any]]:
        """Discover the list of names currently in scope in the current context."""
        res = self.connection.names().result()
        if isinstance(res, list) and all(isinstance(d, dict) and all(isinstance(k, str) for k in d.keys()) for d in res):
            return res
        else:
            raise ValueError("Panic! Result of `names()` is malformed: " + str(res))

    def focused_module(self) -> Dict[str,Any]:
        """Returns the name and other information about the currently-focused module."""
        res = self.connection.focused_module().result()
        if isinstance(res, dict) and all(isinstance(k, str) for k in res.keys()):
            return res
        else:
            raise ValueError("Panic! Result of `focused_module()` is malformed: " + str(res))

    def reset(self) -> None:
        """Resets the connection, causing its unique state on the server to be freed (if applicable).
        After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
        self.connection.reset()

    def reset_server(self) -> None:
        """Resets the Cryptol server, clearing all states."""
        self.connection.reset_server()

    def logging(self, on : bool, *, dest : TextIO = sys.stderr) -> None:
        """Whether to log received and transmitted JSON."""
        self.connection.server_connection.logging(on=on,dest=dest)
