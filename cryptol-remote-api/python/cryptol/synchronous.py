"""A synchronous, typed interface for the Cryptol bindings"""

from __future__ import annotations

import sys
from typing import Any, Optional, Union, List, Dict, TextIO, overload
from typing_extensions import Literal
from dataclasses import dataclass

from .custom_fstring import *
from .quoting import *
from .solver import OfflineSmtQuery, Solver, OnlineSolver, OfflineSolver, Z3
from . import connection
from . import cryptoltypes
from .commands import *
from . import CryptolConnection, SmtQueryType


@dataclass
class Qed:
    """The positive result of a 'prove' SMT query. All instances of this class
    are truthy, i.e. evaluate to `True` in an 'if' or 'while' statement.
    """
    def __bool__(self) -> Literal[True]:
        return True
    def __nonzero__(self) -> Literal[True]:
        return True

@dataclass
class Safe:
    """The positive result of a 'safe' SMT query. All instances of this class
    are truthy, i.e. evaluate to `True` in an 'if' or 'while' statement.
    """
    def __bool__(self) -> Literal[True]:
        return True
    def __nonzero__(self) -> Literal[True]:
        return True

@dataclass
class Counterexample:
    """The negative result of a 'prove' or 'safe' SMT query, consisting of a
    type (either "predicate falsified" or "safety violation") and the list of
    values which constitute the counterexample. All instances of this class are
    falsy, i.e. evaluate to `False` in an 'if' or 'while' statement. (Note that
    this is different from the behaivor of a plain list, which is truthy iff
    it has nonzero length.)
    """
    type : Union[Literal["predicate falsified"], Literal["safety violation"]]
    assignments : List[CryptolValue]

    def __bool__(self) -> Literal[False]:
        return False
    def __nonzero__(self) -> Literal[False]:
        return False

@dataclass
class Satisfiable:
    """The positive result of a 'sat' SMT query, consisting of a list of
    models, where each model is a list of values satisfying the predicate.
    All instances of this class are truthy, i.e. evaluate to `True` in an 'if'
    or 'while' statement. (Note that this is different from the behaivor of a
    plain list, which is truthy iff it has nonzero length.)
    """
    models : List[List[CryptolValue]]

    def __bool__(self) -> Literal[True]:
        return True
    def __nonzero__(self) -> Literal[True]:
        return True

@dataclass
class Unsatisfiable:
    """The negative result of a 'sat' SMT query. All instances of this class
    are falsy, i.e. evaluate to `False` in an 'if 'or 'while' statement.
    """
    def __bool__(self) -> Literal[False]:
        return False
    def __nonzero__(self) -> Literal[False]:
        return False

@dataclass
class CryptolVersionInfo:
    """
    Class containing version information about the Cryptol server.

    :param rpc_version: The cryptol-remote-api version string.
    :param version: The Cryptol version string.
    :param commit_hash: The string of the git commit hash during the build of Cryptol.
    :param commit_branch: The string of the git commit branch during the build of Cryptol.
    :param commit_dirty: True iff non-committed files were present during the build of Cryptol.
    :param ffi_enabled: True iff the FFI is enabled.
    """
    rpc_version: str
    version: str
    commit_hash: str
    commit_branch: str
    commit_dirty: bool
    ffi_enabled: bool 


def connect(command : Optional[str]=None,
            *,
            cryptol_path : Optional[str] = None,
            url : Optional[str] = None,
            reset_server : bool = False,
            verify : Union[bool, str] = True,
            log_dest : Optional[TextIO] = None,
            timeout : Optional[float] = None) -> CryptolSyncConnection:
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
    `timeout` property on a `CryptolSyncConnection` or the `get_default_timeout` and
    `set_default_timeout` methods. Method invocations which specify the optional `timeout` keyword
    parameter will cause the default to be ignored for that method.

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
        log_dest=log_dest,
        timeout=timeout))

def connect_stdio(command : str,
                  cryptol_path : Optional[str] = None,
                  log_dest : Optional[TextIO] = None,
                  timeout : Optional[float] = None) -> CryptolSyncConnection:
    """Start a new synchronous connection to a new Cryptol server process.

    :param command: The command to launch the Cryptol server.

    :param cryptol_path: An optional replacement for the contents of
      the ``CRYPTOLPATH`` environment variable.

    :param log_dest: A destination to log JSON requests/responses to, e.g. ``log_dest=sys.stderr``
    will print traffic to ``stderr``, ``log_dest=open('foo.log', 'w')`` will log to ``foo.log``,
    etc.

    :param timeout: Optional default timeout (in seconds) for methods. Can be modified/read via the
    `timeout` property on a `CryptolSyncConnection` or the `get_default_timeout` and
    `set_default_timeout` methods. Method invocations which specify the optional `timeout` keyword
    parameter will cause the default to be ignored for that method.

    """
    return CryptolSyncConnection(connection.connect_stdio(
        command=command,
        cryptol_path=cryptol_path,
        log_dest=log_dest,
        timeout=timeout))


class CryptolSyncConnection:
    """A wrapper of ``CryptolConnection`` with a synchronous, typed interface."""
    connection : CryptolConnection

    def __init__(self, connection : CryptolConnection):
        self.connection = connection

    @property
    def timeout(self) -> Optional[float]:
        return self.connection.timeout
    
    @timeout.setter
    def timeout(self, timeout : Optional[float]) -> None:
        self.connection.timeout = timeout

    def get_default_timeout(self) -> Optional[float]:
        """Get the value of the optional default timeout for methods (in seconds)."""
        return self.connection.get_default_timeout()
    
    def set_default_timeout(self, timeout : Optional[float]) -> None:
        """Set the value of the optional default timeout for methods (in seconds)."""
        self.connection.set_default_timeout(timeout)

    def load_file(self, filename : str, *, timeout:Optional[float] = None) -> None:
        """Load a filename as a Cryptol module, like ``:load`` at the Cryptol
        REPL.
        """
        self.connection.load_file(filename, timeout=timeout).result()

    def load_module(self, module_name : str, *, timeout:Optional[float] = None) -> None:
        """Load a Cryptol module, like ``:module`` at the Cryptol REPL."""
        self.connection.load_module(module_name, timeout=timeout).result()

    def extend_search_path(self, *dir : str, timeout:Optional[float] = None) -> None:
        """Extend the search path for loading Cryptol modules."""
        self.connection.extend_search_path(*dir, timeout=timeout).result()

    def eval(self, expression : Any, *, timeout:Optional[float] = None) -> CryptolValue:
        """Evaluate a Cryptol expression, with the result represented
        according to :ref:`cryptol-json-expression`, with Python datatypes
        standing for their JSON equivalents.
        """
        return from_cryptol_arg(self.connection.eval_raw(expression, timeout=timeout).result())

    def eval_f(self, s : str, *, timeout:Optional[float] = None) -> CryptolValue:
        """Parses the given string like ``cry_f``, then evalues it, with the
        result represented according to :ref:`cryptol-json-expression`, with
        Python datatypes standing for their JSON equivalents.
        """
        expression = to_cryptol_str_customf(s, frames=1, filename="<eval_f>")
        return self.eval(expression, timeout=timeout)

    def call(self, fun : str, *args : List[Any], timeout:Optional[float] = None) -> CryptolValue:
        """Evaluate a Cryptol functiom by name, with the arguments and the
        result represented according to :ref:`cryptol-json-expression`, with
        Python datatypes standing for their JSON equivalents.
        """
        return from_cryptol_arg(self.connection.call_raw(fun, *args, timeout=timeout).result())

    def check(self, expr : Any, *, num_tests : Union[Literal['all'], int, None] = None, timeout:Optional[float] = None) -> CheckReport:
        """Tests the validity of a Cryptol expression with random inputs. The expression must be a function with
        return type ``Bit``.
        If ``num_tests`` is ``"all"`` then the expression is tested exhaustively (i.e., against all possible inputs).
        If ``num_tests`` is omitted, Cryptol defaults to running 100 tests.
        """
        return to_check_report(self.connection.check_raw(expr, num_tests=num_tests, timeout=timeout).result())

    def check_type(self, code : Any, *, timeout:Optional[float] = None) -> Union[cryptoltypes.CryptolType, cryptoltypes.CryptolTypeSchema]:
        """Check the type of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents.
        """
        return cryptoltypes.to_schema_or_type(self.connection.check_type(code, timeout=timeout).result())

    @overload
    def sat(self, expr : Any, solver : OfflineSolver, count : int = 1, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
    @overload
    def sat(self, expr : Any, solver : OnlineSolver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable]: ...
    @overload
    def sat(self, expr : Any, solver : Solver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable, OfflineSmtQuery]: ...

    def sat(self, expr : Any, solver : Solver = Z3, count : int = 1, *, timeout:Optional[float] = None) -> Union[Satisfiable, Unsatisfiable, OfflineSmtQuery]:
        """Check the satisfiability of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`, and return up to
        `count` solutions.
        
        If the given solver is an `OnlineSolver`, the result is either an
        instance of `Satisfiable`, which is always truthy, or `Unsatisfiable`,
        which is always falsy - meaning the result will evaluate to `True` in
        an 'if' or 'while' statement iff the given expression is satisfiable.
        If the given solver is an `OfflineSolver`, an error will be raised if
        the result is used in an 'if' or 'while' statement.
        """
        if isinstance(solver, OfflineSolver):
            res = self.connection.sat_raw(expr, solver, count, timeout=timeout).result()
            if res['result'] == 'offline':
                return OfflineSmtQuery(res['query'])
            else:
                raise ValueError("Expected an offline SMT result, got: " + str(res))
        elif isinstance(solver, OnlineSolver):
            res = self.connection.sat_raw(expr, solver, count, timeout=timeout).result()
            if res['result'] == 'unsatisfiable':
                return Unsatisfiable()
            elif res['result'] == 'satisfied':
                return Satisfiable([[from_cryptol_arg(arg['expr']) for arg in m] for m in res['models']])
            else:
                raise ValueError("Unexpected 'sat' SMT result: " + str(res))
        else:
            raise ValueError("Unknown solver type: " + str(solver))

    @overload
    def prove(self, expr : Any, solver : OfflineSolver, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
    @overload
    def prove(self, expr : Any, solver : OnlineSolver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample]: ...
    @overload
    def prove(self, expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample, OfflineSmtQuery]: ...

    def prove(self, expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Qed, Counterexample, OfflineSmtQuery]:
        """Check the validity of a Cryptol expression, represented according to
        :ref:`cryptol-json-expression`, with Python datatypes standing for
        their JSON equivalents. Use the solver named `solver`.
        
        If the given solver is an `OnlineSolver`, the result is either an
        instance of `Qed`, which is always truthy, or `Counterexample`, which
        is always falsy - meaning the result will evaluate to `True` in an 'if'
        or 'while' statement iff the given expression can be proved. If the
        given solver is an `OfflineSolver`, an error will be raised if the
        result is used in an 'if' or 'while' statement.
        """
        if isinstance(solver, OfflineSolver):
            res = self.connection.prove_raw(expr, solver, timeout=timeout).result()
            if res['result'] == 'offline':
                return OfflineSmtQuery(res['query'])
            else:
                raise ValueError("Expected an offline SMT result, got: " + str(res))
        elif isinstance(solver, OnlineSolver):
            res = self.connection.prove_raw(expr, solver, timeout=timeout).result()
            if res['result'] == 'unsatisfiable':
                return Qed()
            elif res['result'] == 'invalid':
                return Counterexample(res['counterexample type'], [from_cryptol_arg(arg['expr']) for arg in res['counterexample']])
            else:
                raise ValueError("Unexpected 'prove' SMT result: " + str(res))
        else:
            raise ValueError("Unknown solver type: " + str(solver))

    @overload
    def safe(self, expr : Any, solver : OfflineSolver, *, timeout:Optional[float] = None) -> OfflineSmtQuery: ...
    @overload
    def safe(self, expr : Any, solver : OnlineSolver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample]: ...
    @overload
    def safe(self, expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample, OfflineSmtQuery]: ...

    def safe(self, expr : Any, solver : Solver = Z3, *, timeout:Optional[float] = None) -> Union[Safe, Counterexample, OfflineSmtQuery]:
        """Check via an external SMT solver that the given term is safe for all inputs,
        which means it cannot encounter a run-time error.
        
        If the given solver is an `OnlineSolver`, the result is either an
        instance of `Safe`, which is always truthy, or `Counterexample`, which
        is always falsy - meaning the result will evaluate to `True` in an 'if'
        or 'while' statement iff the given expression is safe. If the given
        solver is an `OfflineSolver`, an error will be raised if the result is
        used in an 'if' or 'while' statement.
        """
        if isinstance(solver, OfflineSolver):
            res = self.connection.safe_raw(expr, solver, timeout=timeout).result()
            if res['result'] == 'offline':
                return OfflineSmtQuery(res['query'])
            else:
                raise ValueError("Expected an offline SMT result, got: " + str(res))
        elif isinstance(solver, OnlineSolver):
            res = self.connection.safe_raw(expr, solver, timeout=timeout).result()
            if res['result'] == 'unsatisfiable':
                return Safe()
            elif res['result'] == 'invalid':
                return Counterexample(res['counterexample type'], [from_cryptol_arg(arg['expr']) for arg in res['counterexample']])
            else:
                raise ValueError("Unexpected 'safe' SMT result: " + str(res))
        else:
            raise ValueError("Unknown solver type: " + str(solver))

    def names(self, *, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
        """Discover the list of term names currently in scope in the current context."""
        res = self.connection.names(timeout=timeout).result()
        if isinstance(res, list):
            return [ cryptoltypes.to_cryptol_name_info(entry) for entry in res ]
        else:
            raise ValueError("Result of `names()` is not a list: " + str(res))

    def parameter_names(self, *, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
        """Discover the list of module parameter names currently in scope in the current context.
        The result is a subset of the list returned by `names`."""
        res = self.connection.parameter_names(timeout=timeout).result()
        if isinstance(res, list):
            return [ cryptoltypes.to_cryptol_name_info(entry) for entry in res ]
        else:
            raise ValueError("Result of `parameter_names()` is not a list: " + str(res))

    def property_names(self, *, timeout:Optional[float] = None) -> List[cryptoltypes.CryptolNameInfo]:
        """Discover the list of property names currently in scope in the current context.
        The result is a subset of the list returned by `names`."""
        res = self.connection.property_names(timeout=timeout).result()
        if isinstance(res, list):
            return [ cryptoltypes.to_cryptol_name_info(entry) for entry in res ]
        else:
            raise ValueError("Result of `property_names()` is not a list: " + str(res))

    def focused_module(self, *, timeout:Optional[float] = None) -> cryptoltypes.CryptolModuleInfo:
        """Returns the name and other information about the currently-focused module."""
        return cryptoltypes.to_cryptol_module_info(self.connection.focused_module(timeout=timeout).result())

    def version(self, *, timeout:Optional[float] = None) -> CryptolVersionInfo:
        """Returns version information about the Cryptol server."""
        res = self.connection.version(timeout=timeout).result()
        return CryptolVersionInfo(
                rpc_version   = res['RPC server version'],
                version       = res['version'],
                commit_hash   = res['commit hash'],
                commit_branch = res['commit branch'],
                commit_dirty  = res['commit dirty'],
                ffi_enabled   = res['FFI enabled']
                )

    def reset(self) -> None:
        """Resets the connection, causing its unique state on the server to be freed (if applicable).
        After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
        self.connection.reset()

    def reset_server(self) -> None:
        """Resets the Cryptol server, clearing all states."""
        self.connection.reset_server()

    def interrupt(self) -> None:
        """Interrupt the Cryptol server, cancelling any in-progress requests."""
        self.connection.interrupt()

    def logging(self, on : bool, *, dest : TextIO = sys.stderr) -> None:
        """Whether to log received and transmitted JSON."""
        self.connection.server_connection.logging(on=on,dest=dest)

    def file_deps( self
                 , m : str, isFile:bool
                 , timeout:Optional[float] = None) -> Any:
        """Get information about a module or a file."""
        return self.connection.file_deps(m,isFile,timeout=timeout).result()
