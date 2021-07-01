
from __future__ import annotations

import base64
from enum import Enum
from dataclasses import dataclass
from typing import Any, List, Optional, Union
from typing_extensions import Literal

import argo_client.interaction as argo
from argo_client.interaction import HasProtocolState
from .solver import Solver, OfflineSmtQuery
from .bitvector import BV
from .opaque import OpaqueValue


def extend_hex(string : str) -> str:
    if len(string) % 2 == 1:
        return '0' + string
    else:
        return string

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
        elif tag == 'variable':
            return OpaqueValue(str(val['identifier']))
        else:
            raise ValueError("Unknown expression tag " + tag)
    else:
        raise TypeError("Unsupported value " + str(val))


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

class CryptolExtendSearchPath(argo.Command):
    def __init__(self, connection : HasProtocolState, dirs : List[str]) -> None:
        super(CryptolExtendSearchPath, self).__init__('extend search path', {'paths': dirs}, connection)

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
        return from_cryptol_arg(res['value'])

class CryptolCall(argo.Command):
    def __init__(self, connection : HasProtocolState, fun : str, args : List[Any]) -> None:
        super(CryptolCall, self).__init__(
            'call',
            {'function': fun, 'arguments': args},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return from_cryptol_arg(res['value'])


@dataclass
class CheckReport:
    """Class for describing ``check`` test results."""
    success: bool
    args: List[Any]
    error_msg: Optional[str]
    tests_run: int
    tests_possible: Optional[int]

class CryptolCheck(argo.Command):
    def __init__(self, connection : HasProtocolState, expr : Any, num_tests : Union[Literal['all'],int, None]) -> None:
        if num_tests:
            args = {'expression': expr, 'number of tests':num_tests}
        else:
            args = {'expression': expr}
        super(CryptolCheck, self).__init__(
            'check',
            args,
            connection
        )

    def process_result(self, res : Any) -> 'CheckReport':
        if res['result'] == 'pass':
            return CheckReport(
                    success=True,
                    args=[],
                    error_msg = None,
                    tests_run=res['tests run'],
                    tests_possible=res['tests possible'])
        elif res['result'] == 'fail':
            return CheckReport(
                    success=False,
                    args=[from_cryptol_arg(arg['expr']) for arg in res['arguments']],
                    error_msg = None,
                    tests_run=res['tests run'],
                    tests_possible=res['tests possible'])
        elif res['result'] == 'error':
            return CheckReport(
                    success=False,
                    args=[from_cryptol_arg(arg['expr']) for arg in res['arguments']],
                    error_msg = res['error message'],
                    tests_run=res['tests run'],
                    tests_possible=res['tests possible'])
        else:
            raise ValueError("Unknown check result " + str(res))


class CryptolCheckType(argo.Command):
    def __init__(self, connection : HasProtocolState, expr : Any) -> None:
        super(CryptolCheckType, self).__init__(
            'check type',
            {'expression': expr},
            connection
        )

    def process_result(self, res : Any) -> Any:
        return res['type schema']

class SmtQueryType(str, Enum):
    PROVE = 'prove'
    SAFE  = 'safe'
    SAT   = 'sat'

class CryptolProveSat(argo.Command):
    def __init__(self, connection : HasProtocolState, qtype : SmtQueryType, expr : Any, solver : Solver, count : Optional[int]) -> None:
        super(CryptolProveSat, self).__init__(
            'prove or satisfy',
            {'query type': qtype,
             'expression': expr,
             'prover': solver.name(),
             'hash consing': "true" if solver.hash_consing() else "false",
             'result count': 'all' if count is None else count},
            connection
        )
        self.qtype = qtype

    def process_result(self, res : Any) -> Any:
        if res['result'] == 'unsatisfiable':
            if self.qtype == SmtQueryType.SAT:
                return False
            elif self.qtype == SmtQueryType.PROVE or self.qtype == SmtQueryType.SAFE:
                return True
            else:
                raise ValueError("Unknown SMT query type: " + self.qtype)
        elif res['result'] == 'invalid':
            return [from_cryptol_arg(arg['expr'])
                    for arg in res['counterexample']]
        elif res['result'] == 'satisfied':
            return [from_cryptol_arg(arg['expr'])
                    for m in res['models']
                    for arg in m]
        elif res['result'] == 'offline':
            return OfflineSmtQuery(content=res['query'])
        else:
            raise ValueError("Unknown SMT result: " + str(res))

class CryptolProve(CryptolProveSat):
    def __init__(self, connection : HasProtocolState, expr : Any, solver : Solver) -> None:
        super(CryptolProve, self).__init__(connection, SmtQueryType.PROVE, expr, solver, 1)

class CryptolSat(CryptolProveSat):
    def __init__(self, connection : HasProtocolState, expr : Any, solver : Solver, count : int) -> None:
        super(CryptolSat, self).__init__(connection, SmtQueryType.SAT, expr, solver, count)

class CryptolSafe(CryptolProveSat):
    def __init__(self, connection : HasProtocolState, expr : Any, solver : Solver) -> None:
        super(CryptolSafe, self).__init__(connection, SmtQueryType.SAFE, expr, solver, 1)

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
