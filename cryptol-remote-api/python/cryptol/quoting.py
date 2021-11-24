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

       Like f-strings, values in brackets (``{``, ``}``) are parsed as python
       expressions in the caller's context of local and global variables, and
       to include a literal bracket in the final string, it must be doubled
       (i.e. ``{{`` or ``}}``). The latter is needed when using explicit type
       application or record syntax. For example, if ``x = [0,1]`` then
       ``cry_f('length `{{2}} {x}')`` is equal to ``cry('length `{2} [0,1]')``
       and ``cry_f('{{ x = {x} }}')`` is equal to ``cry('{ x = [0,1] }')``.

       When formatting Cryptol, it is recomended to always use this function
       and never any of python's built-in methods of string formatting (e.g.
       f-strings, ``str.format``) as the latter will not always produce valid
       cryptol syntax. Specifically, this function differs from these methods
       in the cases of ``BV``s, string literals, function application (this
       function will add parentheses as needed), and dicts. For example,
       ``cry_f('{ {"x": 5, "y": 4} }')`` equals ``cry('{x = 5, y = 4}')``
       but ``f'{ {"x": 5, "y": 4} }'`` equals ``'{"x": 5, "y": 4}'``. Only
       the former is valid cryptol syntax for a record.

       :example:

       >>> x = BV(size=7, value=1)
       >>> y = cry_f('fun1 {x}')
       >>> cry_f('fun2 {y}')
       'fun2 (fun1 (1 : [7]))'
    """
    return CryptolLiteral(func_customf(s, to_cryptol_str, frames=1, filename="<cry_f>"))
