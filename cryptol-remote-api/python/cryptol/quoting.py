"""Cryptol quasiquotation using an f-string-like syntax"""

from typing import Any, Union

from .bitvector import BV
from .opaque import OpaqueValue
from .commands import CryptolValue
from .cryptoltypes import CryptolJSON, CryptolLiteral, parenthesize
from .custom_fstring import *

def to_cryptol_str(val : Union[CryptolValue, str, CryptolJSON]) -> str:
    """Converts a ``CryptolValue``, string literal, or ``CryptolJSON`` into
       a string of Cryptol syntax."""
    if isinstance(val, bool):
        return 'True' if val else 'False'
    elif isinstance(val, tuple):
        if len(val) == 1:
            raise TypeError("Unable to convert 1-tuple to Cryptol syntax: " + str(val))
        return '(' + ', '.join(to_cryptol_str(x) for x in val) + ')'
    elif isinstance(val, dict):
        return '{' + ', '.join(f'{k} = {to_cryptol_str(v)}' for k,v in val.items()) + '}'
    elif isinstance(val, int):
        return str(val)
    elif isinstance(val, list):
        return '[' + ', '.join(to_cryptol_str(x) for x in val) + ']'
    elif isinstance(val, BV):
        if val.size() > 0 and val.size() % 4 == 0:
            return val.hex()
        else:
            return f'({val.to_signed_int()} : [{val.size()}])'
    elif isinstance(val, OpaqueValue):
        return str(val)
    elif isinstance(val, str):
        chars = list(val.encode('latin-1'))
        return f'({to_cryptol_str(chars)} : [{len(chars)}][8])'
    elif hasattr(val, '__to_cryptol_str__'):
        return parenthesize(val.__to_cryptol_str__())
    else:
        raise TypeError("Unable to convert value to Cryptol syntax: " + str(val))

def to_cryptol_str_customf(s : str, *, frames : int = 0,
                                       filename : str = "<cry_f>") -> str:
    """The function used to parse strings given to ``cry_f``"""
    return func_customf(s, to_cryptol_str, frames=1+frames,
                                           filename=filename)

def cry(s : str) -> CryptolLiteral:
    """Embed a string of Cryptol syntax as ``CryptolCode``"""
    return CryptolLiteral(s)

def cry_f(s : str) -> CryptolLiteral:
    """Embed a string of Cryptol syntax as ``CryptolCode``, where the given
       string is parsed as an f-string, and the values within brackets are
       converted to Cryptol syntax using ``to_cryptol_str``.

       Like f-strings, values in brackets (``{``, ``}``) are parsed as python
       expressions in the caller's context of local and global variables, and
       to include a literal bracket in the final string, it must be doubled
       (i.e. ``{{`` or ``}}``). The latter is needed when using explicit type
       application or record syntax. For example, if ``x = [0,1]`` then
       ``cry_f('length `{{2}} {x}')`` is equal to ``cry('length `{2} [0,1]')``
       and ``cry_f('{{ x = {x} }}')`` is equal to ``cry('{ x = [0,1] }')``.

       When formatting Cryptol, it is recomended to use this function rather
       than any of python's built-in methods of string formatting (e.g.
       f-strings, ``str.format``) as the latter will not always produce valid
       Cryptol syntax. Specifically, this function differs from these methods
       in the cases of ``BV``s, string literals, function application (this
       function will add parentheses as needed), and dicts. For example,
       ``cry_f('{ {"x": 5, "y": 4} }')`` equals ``cry('{x = 5, y = 4}')``
       but ``f'{ {"x": 5, "y": 4} }'`` equals ``'{"x": 5, "y": 4}'``. Only
       the former is valid Cryptol syntax for a record.
       
       Note that any conversion or format specifier will always result in the
       argument being rendered as a Cryptol string literal with the conversion
       and/or formating applied. For example, `cry('f {5}')` is equal to
       ``cry('f 5')`` but ``cry_f('f {5!s}')`` is equal to ``cry(`f "5"`)``
       and ``cry_f('f {5:+.2%}')`` is equal to ``cry('f "+500.00%"')``.

       :example:

       >>> x = BV(size=7, value=1)
       >>> y = cry_f('fun1 {x}')
       >>> cry_f('fun2 {y}')
       'fun2 (fun1 (1 : [7]))'
    """
    return CryptolLiteral(to_cryptol_str_customf(s, frames=1))
