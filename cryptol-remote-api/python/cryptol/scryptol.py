"""A synchronous, single-connection interface for the Cryptol bindings"""

from __future__ import annotations

from typing import Optional, Union
from typing_extensions import Literal

from . import solver
from . import commands
from . import connection


__designated_connection = None  # type: Optional[cryptol.CryptolConnection]

def __get_designated_connection() -> connection.CryptolConnection:
    global __designated_connection
    if __designated_connection is None:
        raise ValueError("There is not yet a designated connection.")
    else:
        return __designated_connection


def __set_designated_connection(conn: connection.CryptolConnection) -> None:
    global __designated_connection
    if __designated_connection is None:
        __designated_connection = conn
    else:
        raise ValueError("There is already a designated connection."
                         " Did you call `connect()` more than once?")

def connected() -> bool:
    global __designated_connection
    return __designated_connection is not None


def connect(command : Optional[str]=None,
            *,
            cryptol_path : Optional[str] = None,
            url : Optional[str] = None,
            reset_server : bool = False) -> None:
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
    global __designated_connection
    
    # Set the designated connection by starting a server process
    if __designated_connection is None:
        __designated_connection = connection.connect(
            command=command,
            cryptol_path=cryptol_path,
            url=url,
            reset_server=reset_server)
    elif reset_server:
        __designated_connection.reset_server()
    else:
        raise ValueError("There is already a designated connection."
                         " Did you call `connect()` more than once?")

def connect_stdio(command : str, cryptol_path : Optional[str] = None) -> None:
    """Start a new connection to a new Cryptol server process.

    :param command: The command to launch the Cryptol server.

    :param cryptol_path: An optional replacement for the contents of
      the ``CRYPTOLPATH`` environment variable.

    """
    __set_designated_connection(connection.connect_stdio(
        command=command,
        cryptol_path=cryptol_path))


def load_file(filename : str) -> Any:
    """Load a filename as a Cryptol module, like ``:load`` at the Cryptol
    REPL.
    """
    return __get_designated_connection().load_file(filename).result()

def load_module(module_name : str) -> Any:
    """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
    return __get_designated_connection().load_module(module_name).result()

def eval(expression : Any) -> Any:
    """Evaluate a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing
    for their JSON equivalents.
    """
    res = __get_designated_connection().eval(expression).result()
    return commands.from_cryptol_arg(res['value'])

def evaluate_expression(expression : Any) -> Any:
    """Synonym for ``eval``.
    """
    return eval(expression)

def extend_search_path(*dir : str) -> Any:
    return __get_designated_connection().extend_search_path(*dir).result()

def call(fun : str, *args : List[Any]) -> Any:
    return __get_designated_connection().call(fun, *args).result()

def check(expr : Any, *, num_tests : Union[Literal['all'], int, None] = None) -> commands.CheckReport:
    """Tests the validity of a Cryptol expression with random inputs. The expression must be a function with
    return type ``Bit``.

    If ``num_tests`` is ``"all"`` then the expression is tested exhaustively (i.e., against all possible inputs).

    If ``num_tests`` is omitted, Cryptol defaults to running 100 tests.
    """
    return __get_designated_connection().check(expr, num_tests=num_tests).result()

def check_type(code : Any) -> Any:
    """Check the type of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents.
    """
    return __get_designated_connection().check_type(code).result()

def sat(expr : Any, solver : solver.Solver = solver.Z3, count : int = 1) -> Any:
    """Check the satisfiability of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents. Use the solver named `solver`, and return up to
    `count` solutions.
    """
    return __get_designated_connection().sat(expr, solver, count).result()

def prove(expr : Any, solver : solver.Solver = solver.Z3) -> Any:
    """Check the validity of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents. Use the solver named `solver`.
    """
    return __get_designated_connection().prove(expr, solver).result()

def safe(expr : Any, solver : solver.Solver = solver.Z3) -> Any:
    """Check via an external SMT solver that the given term is safe for all inputs,
    which means it cannot encounter a run-time error.
    """
    return __get_designated_connection().safe(expr, solver).result()

def names() -> Any:
    """Discover the list of names currently in scope in the current context."""
    return __get_designated_connection().names().result()

def focused_module() -> Any:
    """Return the name of the currently-focused module."""
    return __get_designated_connection().focused_module().result()

def reset() -> None:
    """Resets the connection, causing its unique state on the server to be freed (if applicable).

    After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
    __get_designated_connection().reset()

def reset_server() -> None:
    """Resets the Cryptol server, clearing all states."""
    __get_designated_connection().reset_server()
