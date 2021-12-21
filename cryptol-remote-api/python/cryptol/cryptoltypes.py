from __future__ import annotations
from collections import OrderedDict
from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
import base64
from math import ceil
import BitVector #type: ignore
from .bitvector import BV
from .opaque import OpaqueValue

import typing
from typing import cast, Any, Dict, Iterable, List, NoReturn, Optional, TypeVar, Union
import typing_extensions
from typing_extensions import Protocol, runtime_checkable

A = TypeVar('A')


# -----------------------------------------------------------
# CryptolJSON and CryptolCode
# -----------------------------------------------------------

def is_parenthesized(s : str) -> bool:
    """Returns ``True`` iff the given string has balanced parentheses and is
       enclosed in a matching pair of parentheses.
       
       :examples:
       
       >>> is_parenthesized(' ((a) b )')
       True
       >>> is_parenthesized('(a) (b)')
       False
       >>> is_parenthesized('(a')
       False
       """
    seen_one, depth = False, 0
    for c in s:
        if depth > 0:
            if c == '(': depth += 1
            if c == ')': depth -= 1
        else: # depth == 0
            if c == '(':
                if not seen_one: seen_one, depth = True, 1
                # A new left paren after all parens have been closed means our
                #  string is not enclosed in a matching pair of parentheses
                else: return False
            if c == ')':
                # A right paren with no matching left means our string does
                #  not have balanced parentheses
                return False
    # Return True if in the end all parentheses are balanced and we've seen at
    #  least one matching pair
    return seen_one and depth == 0

def parenthesize(s : str) -> str:
    """Encloses the given string ``s`` in parentheses if
       ``is_parenthesized(s)`` is ``False``"""
    return s if is_parenthesized(s) else f'({s})'

JSON = Union[bool, int, float, str, Dict, typing.Tuple, List]

@runtime_checkable
class CryptolJSON(Protocol):
    """A ``Protocol`` for objects which can be converted to Cryptol JSON or
       Cryptol strings."""
    def __to_cryptol__(self) -> JSON: ...
    def __to_cryptol_str__(self) -> str: ...

class CryptolCode(metaclass=ABCMeta):
    """The base class for ``CryptolLiteral`` and ``CryptolApplication``."""
    @abstractmethod
    def __to_cryptol__(self) -> JSON: ...
    @abstractmethod
    def __to_cryptol_str__(self) -> str: ...

    def __str__(self) -> str:
        return self.__to_cryptol_str__()

    def __call__(self, *others : CryptolJSON) -> CryptolCode:
        return CryptolApplication(self, *others)

@dataclass
class CryptolLiteral(CryptolCode):
    """A string of Cryptol syntax."""
    _code : str

    def __to_cryptol__(self) -> JSON:
        return self._code

    def __to_cryptol_str__(self) -> str:
        return self._code

@dataclass
class CryptolApplication(CryptolCode):
    """An application of a Cryptol function to some arguments."""
    _rator : CryptolJSON
    _rands : typing.Sequence[CryptolJSON]

    def __init__(self, rator : CryptolJSON, *rands : CryptolJSON) -> None:
        if all(isinstance(rand, CryptolJSON) for rand in rands):
            self._rator = rator
            self._rands = rands
        else:
            raise ValueError("Arguments given to CryptolApplication must be CryptolJSON")

    def __repr__(self) -> str:
        return f'CryptolApplication({", ".join(repr(x) for x in [self._rator, *self._rands])})'

    def __to_cryptol__(self) -> JSON:
        return {'expression': 'call',
                'function': to_cryptol(self._rator),
                'arguments': [to_cryptol(arg) for arg in self._rands]}

    def __to_cryptol_str__(self) -> str:
        if len(self._rands) == 0:
            return self._rator.__to_cryptol_str__()
        else:
            return ' '.join(parenthesize(x.__to_cryptol_str__()) for x in [self._rator, *self._rands])


# -----------------------------------------------------------
# Cryptol kinds
# -----------------------------------------------------------

@dataclass
class CryptolArrowKind:
    domain : CryptolKind
    range : CryptolKind

CryptolKind = Union[typing_extensions.Literal['Type'],
                    typing_extensions.Literal['Num'],
                    typing_extensions.Literal['Prop'], CryptolArrowKind]

def to_kind(k : Any) -> CryptolKind:
    if k == "Type": return "Type"
    elif k == "Num": return "Num"
    elif k == "Prop": return "Prop"
    elif k['kind'] == "arrow":
        return CryptolArrowKind(k['from'], k['to'])
    else:
        raise ValueError(f'Not a Cryptol kind: {k!r}')


# -----------------------------------------------------------
# Cryptol props
# -----------------------------------------------------------

class CryptolProp:
    pass

@dataclass
class UnaryProp(CryptolProp):
    subject : CryptolType

@dataclass
class BinaryProp(CryptolProp):
    left : CryptolType
    right : CryptolType

@dataclass
class Equal(BinaryProp): pass
@dataclass
class NotEqual(BinaryProp): pass
@dataclass
class Geq(BinaryProp): pass
@dataclass
class Fin(UnaryProp): pass

@dataclass
class Zero(UnaryProp): pass
@dataclass
class Logic(UnaryProp): pass
@dataclass
class Ring(UnaryProp): pass
@dataclass
class Integral(UnaryProp): pass
@dataclass
class Field(UnaryProp): pass
@dataclass
class Round(UnaryProp): pass
@dataclass
class Eq(UnaryProp): pass
@dataclass
class Cmp(UnaryProp): pass
@dataclass
class SignedCmp(UnaryProp): pass
@dataclass
class Literal(CryptolProp):
    size : CryptolType
    subject : CryptolType

@dataclass
class And(CryptolProp):
    left : CryptolProp
    right : CryptolProp
@dataclass
class TrueProp(CryptolProp):
    pass

def to_prop(obj : Any) -> CryptolProp:
    """Convert a Cryptol JSON proposition to a ``CryptolProp``."""
    if obj['prop'] == '==':
        return Equal(to_type(obj['left']), to_type(obj['right']))
    elif obj['prop'] == '!=':
        return NotEqual(to_type(obj['left']), to_type(obj['right']))
    elif obj['prop'] == '>=':
        return Geq(to_type(obj['greater']), to_type(obj['less']))
    elif obj['prop'] == 'fin':
        return Fin(to_type(obj['subject']))
    elif obj['prop'] == 'Ring':
        return Ring(to_type(obj['subject']))
    elif obj['prop'] == 'Field':
        return Field(to_type(obj['subject']))
    elif obj['prop'] == 'Round':
        return Round(to_type(obj['subject']))
    elif obj['prop'] == 'Integral':
        return Integral(to_type(obj['subject']))
    elif obj['prop'] == 'Cmp':
        return Cmp(to_type(obj['subject']))
    elif obj['prop'] == 'SignedCmp':
        return SignedCmp(to_type(obj['subject']))
    elif obj['prop'] == 'Literal':
        return Literal(to_type(obj['size']), to_type(obj['subject']))
    elif obj['prop'] == 'Zero':
        return Zero(to_type(obj['subject']))
    elif obj['prop'] == 'Logic':
        return Logic(to_type(obj['subject']))
    elif obj['prop'] == 'True':
        return TrueProp()
    elif obj['prop'] == 'And':
        return And(to_prop(obj['left']), to_prop(obj['right']))
    else:
        raise NotImplementedError(f"to_prop({obj!r})")


# -----------------------------------------------------------
# Converting Python terms to Cryptol JSON
# -----------------------------------------------------------

def to_cryptol(val : Any) -> JSON:
    """Convert a ``CryptolJSON`` value, a Python value representing a Cryptol
       term, or any combination of the two to Cryptol JSON."""
    if isinstance(val, bool):
        return val
    elif isinstance(val, tuple) and val == ():
        return {'expression': 'unit'}
    elif isinstance(val, tuple):
        return {'expression': 'tuple',
                'data': [to_cryptol(x) for x in val]}
    elif isinstance(val, dict):
        return {'expression': 'record',
                'data': {k : to_cryptol(val[k])
                         if isinstance(k, str)
                         else fail_with (TypeError("Record keys must be strings"))
                         for k in val}}
    elif isinstance(val, int):
        return val
    elif isinstance(val, list):
        return {'expression': 'sequence',
                'data': [to_cryptol(v) for v in val]}
    elif isinstance(val, bytes) or isinstance(val, bytearray):
        return {'expression': 'bits',
                'encoding': 'base64',
                'width': 8 * len(val),
                'data': base64.b64encode(val).decode('ascii')}
    elif isinstance(val, BitVector.BitVector):
        n = int(val)
        byte_width = ceil(n.bit_length()/8)
        return {'expression': 'bits',
                'encoding': 'base64',
                'width': val.length(), # N.B. original length, not padded
                'data': base64.b64encode(n.to_bytes(byte_width,'big')).decode('ascii')}
    elif isinstance(val, BV):
        return {'expression': 'bits',
                'encoding': 'hex',
                'width': val.size(), # N.B. original length, not padded
                'data': val.hex()[2:]}
    elif isinstance(val, OpaqueValue):
        return {'expression': 'variable',
                'identifier': val.identifier}
    elif hasattr(val, '__to_cryptol__'):
        code = val.__to_cryptol__()
        if is_plausible_json(code):
            # the call to is_plausible_json ensures this cast is OK
            return cast(JSON, code)
        else:
            raise ValueError(f"Improbable JSON from __to_cryptol__: {val!r} gave {code!r}")
    else:
        raise TypeError("Unsupported value: " + str(val))

def fail_with(exn : Exception) -> NoReturn:
    raise exn

def is_plausible_json(val : Any) -> bool:
    for ty in [bool, int, float, str]:
        if isinstance(val, ty): return True

    if isinstance(val, dict):
        return all(isinstance(k, str) and is_plausible_json(val[k]) for k in val)

    if isinstance(val, tuple) or isinstance(val, list):
        return all(is_plausible_json(elt) for elt in val)

    return False


# -----------------------------------------------------------
# Cryptol types
# -----------------------------------------------------------

class CryptolType:
    def from_python(self, val : Any) -> NoReturn:
        raise Exception("CryptolType.from_python is deprecated, use to_cryptol")
    
    def convert(self, val : Any) -> NoReturn:
        raise Exception("CryptolType.convert is deprecated, use to_cryptol")

@dataclass
class Var(CryptolType):
    name : str
    kind : CryptolKind

    def __str__(self) -> str:
        return self.name

@dataclass
class Function(CryptolType):
    domain : CryptolType
    range : CryptolType

    def __str__(self) -> str:
        return f"({self.domain} -> {self.range})"

@dataclass
class Bitvector(CryptolType):
    width : CryptolType

    def __str__(self) -> str:
        return f"[{self.width}]"

@dataclass
class Num(CryptolType):
    number : int

    def __str__(self) -> str:
        return str(self.number)

@dataclass
class Bit(CryptolType):
    def __str__(self) -> str:
        return "Bit"

@dataclass
class Sequence(CryptolType):
    length : CryptolType
    contents : CryptolType

    def __str__(self) -> str:
        return f"[{self.length}]{self.contents}"

@dataclass
class Inf(CryptolType):
    def __str__(self) -> str:
        return "inf"

@dataclass
class Integer(CryptolType):
    def __str__(self) -> str:
        return "Integer"

@dataclass
class Rational(CryptolType):
    def __str__(self) -> str:
        return "Rational"

@dataclass
class Z(CryptolType):
    modulus : CryptolType

    def __str__(self) -> str:
        return f"(Z {self.modulus})"

@dataclass
class BinaryType(CryptolType):
    left : CryptolType
    right : CryptolType

@dataclass
class Plus(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} + {self.right})"

@dataclass
class Minus(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} - {self.right})"

@dataclass
class Times(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} * {self.right})"

@dataclass
class Div(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} / {self.right})"

@dataclass
class CeilDiv(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} /^ {self.right})"

@dataclass
class Mod(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} % {self.right})"

@dataclass
class CeilMod(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} %^ {self.right})"

@dataclass
class Expt(BinaryType):
    def __str__(self) -> str:
        return f"({self.left} ^^ {self.right})"

@dataclass
class Log2(CryptolType):
    operand : CryptolType

    def __str__(self) -> str:
        return f"(lg2 {self.operand})"

@dataclass
class Width(CryptolType):
    operand : CryptolType

    def __str__(self) -> str:
        return f"(width {self.operand})"

@dataclass
class Max(BinaryType):
    def __str__(self) -> str:
        return f"(max {self.left} {self.right})"

@dataclass
class Min(BinaryType):
    def __str__(self) -> str:
        return f"(min {self.left} {self.right})"

@dataclass
class LenFromThenTo(CryptolType):
    num_from : CryptolType
    num_then : CryptolType
    num_to : CryptolType

    def __str__(self) -> str:
        return f"(lengthFromThenTo {self.num_from} {self.num_then} {self.num_to})"

@dataclass
class Tuple(CryptolType):
    types : typing.Sequence[CryptolType]

    def __init__(self, *types : CryptolType) -> None:
        self.types = types

    def __repr__(self) -> str:
        return "Tuple(" + ", ".join(map(repr, self.types)) + ")"

    def __str__(self) -> str:
        return "(" + ",".join(map(str, self.types)) + ")"

@dataclass
class Record(CryptolType):
    fields : Dict[str, CryptolType]

    def __str__(self) -> str:
        return "{" + ",".join(str(k) + " = " + str(self.fields[k]) for k in self.fields) + "}"

def to_type(t : Any) -> CryptolType:
    """Convert a Cryptol JSON type to a ``CryptolType``."""
    if t['type'] == 'variable':
        return Var(t['name'], to_kind(t['kind']))
    elif t['type'] == 'function':
        return Function(to_type(t['domain']), to_type(t['range']))
    elif t['type'] == 'bitvector':
        return Bitvector(to_type(t['width']))
    elif t['type'] == 'number':
        return Num(t['value'])
    elif t['type'] == 'Bit':
        return Bit()
    elif t['type'] == 'sequence':
        return Sequence(to_type(t['length']), to_type(t['contents']))
    elif t['type'] == 'inf':
        return Inf()
    elif t['type'] == '+':
        return Plus(*map(to_type, t['arguments']))
    elif t['type'] == '-':
        return Minus(*map(to_type, t['arguments']))
    elif t['type'] == '*':
        return Times(*map(to_type, t['arguments']))
    elif t['type'] == '/':
        return Div(*map(to_type, t['arguments']))
    elif t['type'] == '/^':
        return CeilDiv(*map(to_type, t['arguments']))
    elif t['type'] == '%':
        return Mod(*map(to_type, t['arguments']))
    elif t['type'] == '%^':
        return CeilMod(*map(to_type, t['arguments']))
    elif t['type'] == '^^':
        return Expt(*map(to_type, t['arguments']))
    elif t['type'] == 'lg2':
        return Log2(*map(to_type, t['arguments']))
    elif t['type'] == 'width':
        return Width(*map(to_type, t['arguments']))
    elif t['type'] == 'max':
        return Max(*map(to_type, t['arguments']))
    elif t['type'] == 'min':
        return Min(*map(to_type, t['arguments']))
    elif t['type'] == 'tuple':
        return Tuple(*map(to_type, t['contents']))
    elif t['type'] == 'unit':
        return Tuple()
    elif t['type'] == 'record':
        return Record({k : to_type(t['fields'][k]) for k in t['fields']})
    elif t['type'] == 'Integer':
        return Integer()
    elif t['type'] == 'Rational':
        return Rational()
    elif t['type'] == 'Z':
        return Z(to_type(t['modulus']))
    else:
        raise NotImplementedError(f"to_type({t!r})")


# -----------------------------------------------------------
# Cryptol type schema
# -----------------------------------------------------------

class CryptolTypeSchema:
    def __init__(self,
                 variables : OrderedDict[str, CryptolKind],
                 propositions : List[Optional[CryptolProp]], # TODO complete me!
                 body : CryptolType) -> None:
        self.variables = variables
        self.propositions = propositions
        self.body = body

    def __repr__(self) -> str:
        return f"CryptolTypeSchema({self.variables!r}, {self.propositions!r}, {self.body!r})"

def to_schema(obj : Any) -> CryptolTypeSchema:
    """Convert a Cryptol JSON type schema to a ``CryptolTypeSchema``."""
    return CryptolTypeSchema(OrderedDict((v['name'], to_kind(v['kind']))
                                         for v in obj['forall']),
                             [to_prop(p) for p in obj['propositions']],
                             to_type(obj['type']))

def argument_types(obj : Union[CryptolTypeSchema, CryptolType]) -> List[CryptolType]:
    if isinstance(obj, CryptolTypeSchema):
        return argument_types(obj.body)
    elif isinstance(obj, Function):
        arg1 = obj.domain
        args = argument_types(obj.range)
        return [arg1] + args
    else:
        return []
