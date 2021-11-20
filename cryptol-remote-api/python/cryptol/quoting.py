"""Cryptol quasiquotation using an f-string-like syntax"""

from typing import Any, Union

from .bitvector import BV
from .opaque import OpaqueValue
from .commands import CryptolValue
from .cryptoltypes import CryptolLiteral
from .custom_fstring import *

def to_cryptol_str(val : Union[CryptolValue, str, CryptolLiteral]) -> str:
    """Converts a ``CryptolValue``, string literal, or ``CryptolLiteral`` into
       a string of cryptol syntax."""
    if isinstance(val, bool):
        return 'True' if val else 'False'
    elif isinstance(val, tuple):
        return '(' + ', '.join(to_cryptol_str(x) for x in val) + ')'
    elif isinstance(val, dict):
        return '{' + ', '.join(f'{k} = {to_cryptol_str(v)}' for k,v in val.items()) + '}'
    elif isinstance(val, int):
        return str(val)
    elif isinstance(val, list):
        return '[' + ', '.join(to_cryptol_str(x) for x in val) + ']'
    elif isinstance(val, BV):
        if val.size() % 4 == 0:
            return val.hex()
        else:
            return f'({val.to_signed_int()} : [{val.size()}])'
    elif isinstance(val, OpaqueValue):
        return str(val)
    elif isinstance(val, str):
        return f'"{val}"'
    elif isinstance(val, CryptolLiteral):
        if len(str(val)) > 0 and str(val)[0] == '(' and str(val)[-1] == ')':
            return str(val)
        else:
            return f'({val})'
    else:
        raise TypeError("Unable to convert value to Cryptol syntax: " + str(val))

def cry(s : str) -> CryptolLiteral:
    """Embed a string of cryptol syntax as ``CryptolCode``"""
    return CryptolLiteral(s)

def cry_f(s : str) -> CryptolLiteral:
    """Embed a string of cryptol syntax as ``CryptolCode``, where the given
       string is parsed as an f-string, and the values within brackets are
       converted to cryptol syntax using ``to_cryptol_str``.
       
       Example:
           >>> x = BV(size=7, value=1)
           >>> y = cry_f('fun1 {x}')
           >>> cry_f('fun2 {y}')
           'fun2 (fun1 (1 : [7]))'
    """
    return CryptolLiteral(func_customf(s, to_cryptol_str, frames=1, filename="<cry_f>"))
