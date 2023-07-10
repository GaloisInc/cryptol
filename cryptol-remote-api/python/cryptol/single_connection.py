"""A single-connection, synchronous, typed interface for the Cryptol bindings"""

from __future__ import annotations

import sys
from typing import Any, Optional, Union, List, Dict, TextIO, overload
from typing_extensions import Literal

from .custom_fstring import *
from .quoting import *
from .solver import OfflineSmtQuery, Solver, OnlineSolver, OfflineSolver, Z3
from .connection import CryptolValue, CheckReport
from . import synchronous
from .synchronous import Qed, Safe, Counterexample, Satisfiable, Unsatisfiable, CryptolVersionInfo
from . import cryptoltypes


__designated_connection = None  # type: Optional[synchronous.CryptolSyncConnection]

def __get_designated_connection() -> synchronous.CryptolSyncConnection:
    global __designated_connection
    if __designated_connection is None:
        raise ValueError("There is not yet a designated connection.")
    else:
        return __designated_connection

def __set_designated_connection(conn: synchronous.CryptolSyncConnection) -> None:
    global __designated_connection
    __designated_connection = conn

def connected() -> bool:
    global __designated_connection
    return __designated_connection is not None

def connect(command : Optional[str]=None,
            *,
            cryptol_path : Optional[str] = None,
            url : Optional[str] = None,
            reset_server : bool = False,
            verify : Union[bool, str] = True,
            log_dest : Optional[TextIO] = None,
            timeout : Optional[float] = None) -> None:
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

    :param timeout: Optional default timeout (in seconds) for methods. Can be modified/read via the
    the `get_default_timeout` and `set_default_timeout` methods. Method invocations which specify
    the optional `timeout` keyword parameter will cause the default to be ignored for that method.

    If no ``command`` or ``url`` parameters are provided, the following are attempted in order:

    1. If the environment variable ``CRYPTOL_SERVER`` is set and referse to an executable,
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    2. If the environment variable ``CRYPTOL_SERVER_URL`` is set, it is assumed to be
    the URL for a running Cryptol server in ``http`` mode and will be connected to.

    3. If an executable ``cryptol-remote-api`` is available on the ``PATH``
    it is assumed to be a Cryptol server and will be used for a new ``socket`` connection.

    """
    global __designated_connection
    __set_designated_connection(synchronous.connect(
        command=command,
        cryptol_path=cryptol_path,
        url=url,
        reset_server=reset_server,
        verify=verify,
        log_dest=log_dest,
        timeout=timeout))

def connect_stdio(command : str,
                  cryptol_path : Optional[str] = None,
                  log_dest : Optional[TextIO] = None,
                  timeout : Optional[float] = None) -> None:
    """Start a new synchronous connection to a new Cryptol server process.

    :param command: The command to launch the Cryptol server.

    :param cryptol_path: An optional replacement for the contents of
      the ``CRYPTOLPATH`` environment variable.

    :param log_dest: A destination to log JSON requests/responses to, e.g. ``log_dest=sys.stderr``
    will print traffic to ``stderr``, ``log_dest=open('foo.log', 'w')`` will log to ``foo.log``,
    etc.

    :param timeout: Optional default timeout (in seconds) for methods. Can be modified/read via the
    the `get_default_timeout` and `set_default_timeout` methods. Method invocations which specify
    the optional `timeout` keyword parameter will cause the default to be ignored for that method.

    """
    __set_designated_connection(synchronous.connect_stdio(
        command=command,
        cryptol_path=cryptol_path,
        log_dest=log_dest,
        timeout=timeout))


def get_default_timeout() -> Optional[float]:
    """Get the value of the optional default timeout for methods (in seconds)."""
    return __get_designated_connection().get_default_timeout()

def set_default_timeout(timeout : Optional[float]) -> None:
    """Set the value of the optional default timeout for methods (in seconds)."""
    __get_designated_connection().set_default_timeout(timeout)

def load_file(filename : str, *, timeout:Optional[float] = None) -> None:
    """Load a filename as a Cryptol module, like ``:load`` at the Cryptol
    REPL.
    """
    __get_designated_connection().load_file(filename, timeout=timeout)

def load_module(module_name : str, *, timeout:Optional[float] = None) -> None:
    """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
    __get_designated_connection().load_module(module_name, timeout=timeout)

def extend_search_path(*dir : str, timeout:Optional[float] = None) -> None:
    """Extend the search path for loading Cryptol modules."""
    __get_designated_connection().extend_search_path(*dir, timeout=timeout)

def cry_eval(expression : Any, *, timeout:Optional[float] = None) -> CryptolValue:
    """Evaluate a Cryptol expression, with the result represented
    according to :ref:`cryptol-json-expression`, with Python datatypes
    standing for their JSON equivalents.
    """
    return __get_designated_connection().eval(expression, timeout=timeout)

def cry_eval_f(s : str, *, timeout:Optional[float] = None) -> CryptolValue:
    """Parses the given string like ``cry_f``, then evalues it, with the
    result represented according to :ref:`cryptol-json-expression`, with
    Python datatypes standing for their JSON equivalents.
    """
    expression = to_cryptol_str_customf(s, frames=1, filename="<cry_eval_f>")
    return cry_eval(expression, timeout=timeout)

def call(fun : str, *args : List[Any], timeout:Optional[float] = None) -> CryptolValue:
    """Evaluate a Cryptol functiom by name, with the arguments and the
    result represented according to :ref:`cryptol-json-expression`, with
    Python datatypes standing for their JSON equivalents.
    """
    return __get_designated_connection().call(fun, *args, timeout=timeout)

def check(expr : Any, *, num_tests : Union[Literal['all'], int, None] = None, timeout:Optional[float] = None) -> CheckReport:
    """Tests the validity of a Cryptol expression with random inputs. The expression must be a function with
    return type ``Bit``.
    If ``num_tests`` is ``"all"`` then the expression is tested exhaustively (i.e., against all possible inputs).
    If ``num_tests`` is omitted, Cryptol defaults to running 100 tests.
    """
    return __get_designated_connection().check(expr, num_tests=num_tests, timeout=timeout)

def check_type(code : Any, *, timeout:Optional[float] = None) -> Union[cryptoltypes.CryptolType, cryptoltypes.CryptolTypeSchema]:
    """Check the type of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents.
    """
    return __get_designated_connection().check_type(code, timeout=timeout)

@overload
def sat(expr : Any, solver : OfflineSolver, count : int = 1, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
@overload
def sat(expr : Any, solver : OnlineSolver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable]: ...
@overload
def sat(expr : Any, solver : Solver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable, OfflineSmtQuery]: ...

def sat(expr : Any, solver : Solver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable, OfflineSmtQuery]:
    """Check the satisfiability of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents. Use the solver named `solver`, and return up to
    `count` solutions.
    """
    return __get_designated_connection().sat(expr, solver, count, timeout=timeout)

@overload
def prove(expr : Any, solver : OfflineSolver, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
@overload
def prove(expr : Any, solver : OnlineSolver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample]: ...
@overload
def prove(expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample, OfflineSmtQuery]: ...

def prove(expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample, OfflineSmtQuery]:
    """Check the validity of a Cryptol expression, represented according to
    :ref:`cryptol-json-expression`, with Python datatypes standing for
    their JSON equivalents. Use the solver named `solver`.
    """
    return __get_designated_connection().prove(expr, solver, timeout=timeout)

@overload
def safe(expr : Any, solver : OfflineSolver, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
@overload
def safe(expr : Any, solver : OnlineSolver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample]: ...
@overload
def safe(expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample, OfflineSmtQuery]: ...

def safe(expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample, OfflineSmtQuery]:
    """Check via an external SMT solver that the given term is safe for all inputs,
    which means it cannot encounter a run-time error.
    """
    return __get_designated_connection().safe(expr, solver, timeout=timeout)

def names(*, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
    """Discover the list of term names currently in scope in the current context."""
    return __get_designated_connection().names(timeout=timeout)

def parameter_names(*, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
    """Discover the list of module parameter names currently in scope in the current context.
    The result is a subset of the list returned by `names`."""
    return __get_designated_connection().parameter_names(timeout=timeout)

def property_names(*, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
    """Discover the list of property names currently in scope in the current context.
    The result is a subset of the list returned by `names`."""
    return __get_designated_connection().property_names(timeout=timeout)

def focused_module(*, timeout:Optional[float] = None) -> cryptoltypes.CryptolModuleInfo:
    """Returns the name and other information about the currently-focused module."""
    return __get_designated_connection().focused_module(timeout=timeout)

def version(*, timeout:Optional[float] = None) -> CryptolVersionInfo:
    """Returns version information about the Cryptol server."""
    return __get_designated_connection().version(timeout=timeout)

def reset() -> None:
    """Resets the connection, causing its unique state on the server to be freed (if applicable).
    After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
    __get_designated_connection().reset()

def reset_server() -> None:
    """Resets the Cryptol server, clearing all states."""
    __get_designated_connection().reset_server()

def interrupt() -> None:
    """Interrupt the Cryptol server, cancelling any in-progress requests."""
    __get_designated_connection().interrupt()

def logging(on : bool, *, dest : TextIO = sys.stderr) -> None:
    """Whether to log received and transmitted JSON."""
    __get_designated_connection().logging(on=on,dest=dest)

def file_deps(m : str, isFile:bool, timeout:Optional[float] = None) -> Any:
    """Get information about a module or a file."""
    return __get_designated_connection().file_deps(m,isFile,timeout=timeout)


