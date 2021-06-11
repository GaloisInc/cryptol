from __future__ import annotations
from collections import OrderedDict
from abc import ABCMeta, abstractmethod
import base64
from math import ceil
import BitVector #type: ignore
from .bitvector import BV
from .opaque import OpaqueValue

from typing import Any, Dict, Iterable, List, NoReturn, Optional, TypeVar, Union

from typing_extensions import Literal, Protocol

A = TypeVar('A')

class CryptolJSON(Protocol):
    def __to_cryptol__(self, ty : CryptolType) -> Any: ...

class CryptolCode(metaclass=ABCMeta):
    def __call__(self, other : CryptolJSON) -> CryptolCode:
        return CryptolApplication(self, other)

    @abstractmethod
    def __to_cryptol__(self, ty : CryptolType) -> Any: ...


class CryptolLiteral(CryptolCode):
    def __init__(self, code : str) -> None:
        self._code = code

    def __to_cryptol__(self, ty : CryptolType) -> Any:
        return self._code


class CryptolApplication(CryptolCode):
    def __init__(self, rator : CryptolJSON, *rands : CryptolJSON) -> None:
        self._rator = rator
        self._rands = rands

    def __to_cryptol__(self, ty : CryptolType) -> Any:
        return {'expression': 'call',
                'function': to_cryptol(self._rator),
                'arguments': [to_cryptol(arg) for arg in self._rands]}

class CryptolArrowKind:
    def __init__(self, dom : CryptolKind, ran : CryptolKind):
        self.domain = dom
        self.range = ran

    def __repr__(self) -> str:
        return f"CryptolArrowKind({self.domain!r}, {self.range!r})"

CryptolKind = Union[Literal['Type'], Literal['Num'], Literal['Prop'], CryptolArrowKind]

def to_kind(k : Any) -> CryptolKind:
    if k == "Type": return "Type"
    elif k == "Num": return "Num"
    elif k == "Prop": return "Prop"
    elif k['kind'] == "arrow":
        return CryptolArrowKind(k['from'], k['to'])
    else:
        raise ValueError(f'Not a Cryptol kind: {k!r}')

class CryptolProp:
    pass

class UnaryProp(CryptolProp):
    def __init__(self, subject : CryptolType) -> None:
        self.subject = subject

class Fin(UnaryProp):
    def __repr__(self) -> str:
        return f"Fin({self.subject!r})"

class Cmp(UnaryProp):
    def __repr__(self) -> str:
        return f"Cmp({self.subject!r})"

class SignedCmp(UnaryProp):
    def __repr__(self) -> str:
        return f"SignedCmp({self.subject!r})"

class Zero(UnaryProp):
    def __repr__(self) -> str:
        return f"Zero({self.subject!r})"

class Arith(UnaryProp):
    def __repr__(self) -> str:
        return f"Arith({self.subject!r})"

class Logic(UnaryProp):
    def __repr__(self) -> str:
        return f"Logic({self.subject!r})"


def to_cryptol(val : Any, cryptol_type : Optional[CryptolType] = None) -> Any:
    if cryptol_type is not None:
        return cryptol_type.from_python(val)
    else:
        return CryptolType().from_python(val)

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

class CryptolType:
    def from_python(self, val : Any) -> Any:
        if hasattr(val, '__to_cryptol__'):
            code = val.__to_cryptol__(self)
            if is_plausible_json(code):
                return code
            else:
                raise ValueError(f"Improbable JSON from __to_cryptol__: {val!r} gave {code!r}")
            # if isinstance(code, CryptolCode):
            #     return self.convert(code)
            # else:
            #     raise ValueError(f"Expected Cryptol code from __to_cryptol__ on {val!r}, but got {code!r}.")
        else:
            return self.convert(val)

    def convert(self, val : Any) -> Any:
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
        else:
            raise TypeError("Unsupported value: " + str(val))

class Var(CryptolType):
    def __init__(self, name : str, kind : CryptolKind) -> None:
        self.name = name
        self.kind = kind

    def __repr__(self) -> str:
        return f"Var({self.name!r}, {self.kind!r})"



class Function(CryptolType):
    def __init__(self, dom : CryptolType, ran : CryptolType) -> None:
        self.domain = dom
        self.range = ran

    def __repr__(self) -> str:
        return f"Function({self.domain!r}, {self.range!r})"

class Bitvector(CryptolType):
    def __init__(self, width : CryptolType) -> None:
        self.width = width

    def __repr__(self) -> str:
        return f"Bitvector({self.width!r})"

    def convert(self, val : Any) -> Any:
        # XXX figure out what to do when width is not evenly divisible by 8
        if isinstance(val, int):
            w = eval_numeric(self.width, None)
            if w is not None:
                return self.convert(int.to_bytes(val, int(w / 8), 'big', signed=True))
            else:
                raise ValueError(f"Insufficent type information to serialize int as bitvector")
        elif isinstance(val, bytearray) or isinstance(val, bytes):
            return {'expression': 'bits',
                    'encoding': 'base64',
                    'width': eval_numeric(self.width, 8 * len(val)),
                    'data': base64.b64encode(val).decode('ascii')}
        elif isinstance(val, BitVector.BitVector):
            return CryptolType.convert(self, val)
        elif isinstance(val, BV):
            return CryptolType.convert(self, val)
        else:
            raise ValueError(f"Not supported as bitvector: {val!r}")

def eval_numeric(t : Any, default : A) -> Union[int, A]:
    if isinstance(t, Num):
        return t.number
    else:
        return default


class Num(CryptolType):
    def __init__(self, number : int) -> None:
        self.number = number

    def __repr__(self) -> str:
        return f"Num({self.number!r})"

class Bit(CryptolType):
    def __init__(self) -> None:
        pass

    def __repr__(self) -> str:
        return f"Bit()"

class Sequence(CryptolType):
    def __init__(self, length : CryptolType, contents : CryptolType) -> None:
        self.length = length
        self.contents = contents

    def __repr__(self) -> str:
        return f"Sequence({self.length!r}, {self.contents!r})"

class Inf(CryptolType):
    def __repr__(self) -> str:
        return f"Inf()"

class Integer(CryptolType):
    def __repr__(self) -> str:
        return f"Integer()"

class Rational(CryptolType):
    def __repr__(self) -> str:
        return f"Rational()"

class Z(CryptolType):
    def __init__(self, modulus : CryptolType) -> None:
        self.modulus = modulus

    def __repr__(self) -> str:
        return f"Z({self.modulus!r})"


class Plus(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} + {self.right})"

    def __repr__(self) -> str:
        return f"Plus({self.left!r}, {self.right!r})"

class Minus(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} - {self.right})"

    def __repr__(self) -> str:
        return f"Minus({self.left!r}, {self.right!r})"

class Times(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} * {self.right})"

    def __repr__(self) -> str:
        return f"Times({self.left!r}, {self.right!r})"


class Div(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} / {self.right})"

    def __repr__(self) -> str:
        return f"Div({self.left!r}, {self.right!r})"

class CeilDiv(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} /^ {self.right})"

    def __repr__(self) -> str:
        return f"CeilDiv({self.left!r}, {self.right!r})"

class Mod(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} % {self.right})"

    def __repr__(self) -> str:
        return f"Mod({self.left!r}, {self.right!r})"

class CeilMod(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} %^ {self.right})"

    def __repr__(self) -> str:
        return f"CeilMod({self.left!r}, {self.right!r})"

class Expt(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} ^^ {self.right})"

    def __repr__(self) -> str:
        return f"Expt({self.left!r}, {self.right!r})"

class Log2(CryptolType):
    def __init__(self, operand : CryptolType) -> None:
        self.operand = operand

    def __str__(self) -> str:
        return f"(lg2 {self.operand})"

    def __repr__(self) -> str:
        return f"Log2({self.operand!r})"

class Width(CryptolType):
    def __init__(self, operand : CryptolType) -> None:
        self.operand = operand

    def __str__(self) -> str:
        return f"(width {self.operand})"

    def __repr__(self) -> str:
        return f"Width({self.operand!r})"

class Max(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"(max {self.left} {self.right})"

    def __repr__(self) -> str:
        return f"Max({self.left!r}, {self.right!r})"

class Min(CryptolType):
    def __init__(self, left : CryptolType, right : CryptolType) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"(min {self.left} {self.right})"

    def __repr__(self) -> str:
        return f"Min({self.left!r}, {self.right!r})"

class Tuple(CryptolType):
    types : Iterable[CryptolType]

    def __init__(self, *types : CryptolType) -> None:
        self.types = types

    def __repr__(self) -> str:
        return "Tuple(" + ", ".join(map(str, self.types)) + ")"

class Record(CryptolType):
    def __init__(self, fields : Dict[str, CryptolType]) -> None:
        self.fields = fields

    def __repr__(self) -> str:
        return f"Record({self.fields!r})"


def to_type(t : Any) -> CryptolType:
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
    return CryptolTypeSchema(OrderedDict((v['name'], to_kind(v['kind']))
                                         for v in obj['forall']),
                             [to_prop(p) for p in obj['propositions']],
                             to_type(obj['type']))

def to_prop(obj : Any) -> Optional[CryptolProp]:
    if obj['prop'] == 'fin':
        return Fin(to_type(obj['subject']))
    elif obj['prop'] == 'Cmp':
        return Cmp(to_type(obj['subject']))
    elif obj['prop'] == 'SignedCmp':
        return SignedCmp(to_type(obj['subject']))
    elif obj['prop'] == 'Zero':
        return Zero(to_type(obj['subject']))
    elif obj['prop'] == 'Arith':
        return Arith(to_type(obj['subject']))
    elif obj['prop'] == 'Logic':
        return Logic(to_type(obj['subject']))
    else:
        return None
        #raise ValueError(f"Can't convert to a Cryptol prop: {obj!r}")

def argument_types(obj : Union[CryptolTypeSchema, CryptolType]) -> List[CryptolType]:
    if isinstance(obj, CryptolTypeSchema):
        return argument_types(obj.body)
    elif isinstance(obj, Function):
        arg1 = obj.domain
        args = argument_types(obj.range)
        return [arg1] + args
    else:
        return []
