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
from typing_extensions import Protocol, runtime_checkable, TypedDict, NotRequired

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
            args_str = ", ".join(map(repr, [rator, *rands]))
            raise ValueError("Arguments given to CryptolApplication must be CryptolJSON: " + args_str)

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
# Cryptol kinds
# -----------------------------------------------------------

@dataclass
class CryptolArrowKind:
    domain : CryptolKind
    range : CryptolKind

CryptolKind = Union[typing_extensions.Literal['Type'],
                    typing_extensions.Literal['Num'],
                    typing_extensions.Literal['Prop'],
                    CryptolArrowKind]

def to_kind(k : Any) -> CryptolKind:
    if k == "Type": return "Type"
    elif k == "Num": return "Num"
    elif k == "Prop": return "Prop"
    elif k['kind'] == "arrow":
        return CryptolArrowKind(k['from'], k['to'])
    else:
        raise ValueError(f'Not a Cryptol kind: {k!r}')


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
class TypeOp(CryptolType):
    op : str
    args : typing.Sequence[CryptolType]

    # we override the @dataclass __init__ and __repr__ because we want the
    #  syntax of variable numbers of arguments
    def __init__(self, op : str, *args : CryptolType) -> None:
        self.op = op
        self.args = args

    def __repr__(self) -> str:
        return "TypeOp(" + ", ".join(map(repr, [self.op, *self.args])) + ")"

    def __str__(self) -> str:
        if self.op.isalnum():
            return "(" + " ".join(map(str, [self.op, self.args])) + ")"
        elif len(self.args) == 2:
            return f"({self.args[0]} {self.op} {self.args[1]})"
        else:
            raise NotImplementedError(f"__str__ for: {self!r}")

@dataclass
class Tuple(CryptolType):
    types : typing.Sequence[CryptolType]

    # we override the @dataclass __init__ and __repr__ because we want the
    #  syntax of variable numbers of arguments
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
    elif 'arguments' in t:
        return TypeOp(t['type'], *map(to_type, t['arguments']))
    else:
        raise NotImplementedError(f"to_type({t!r})")


# -----------------------------------------------------------
# Cryptol props
# -----------------------------------------------------------

class CryptolProp:
    pass

@dataclass
class PropCon(CryptolProp):
    con : str
    args : typing.Sequence[CryptolType]

    # we override the @dataclass __init__ and __repr__ because we want the
    #  syntax of variable numbers of arguments
    def __init__(self, con : str, *args : CryptolType) -> None:
        self.con = con
        self.args = args

    def __repr__(self) -> str:
        return "PropCon(" + ", ".join(map(repr, [self.con, *self.args])) + ")"

    def __str__(self) -> str:
        if self.con.isalnum():
            return "(" + " ".join(map(str, [self.con, self.args])) + ")"
        elif len(self.args) == 2:
            return f"({self.args[0]} {self.con} {self.args[1]})"
        else:
            raise NotImplementedError(f"__str__ for: {self!r}")

@dataclass
class And(CryptolProp):
    left : CryptolProp
    right : CryptolProp

    def __str__(self) -> str:
        return f"({self.left} && {self.right})"

@dataclass
class TrueProp(CryptolProp):
    def __str__(self) -> str:
        return "True"

def to_prop(obj : Any) -> CryptolProp:
    """Convert a Cryptol JSON proposition to a ``CryptolProp``."""
    if obj['prop'] == 'And':
        return And(to_prop(obj['left']), to_prop(obj['right']))
    elif obj['prop'] == 'True':
        return TrueProp()
    # special cases for props which have irregular JSON structure
    elif obj['prop'] == 'Literal':
        return PropCon('Literal', to_type(obj['size']), to_type(obj['subject']))
    elif obj['prop'] == '>=':
        return PropCon('>=', to_type(obj['greater']), to_type(obj['less']))
    # general cases for unary, binary, and unknown props
    elif 'subject' in obj and len(obj) == 2:
        return PropCon(obj['prop'], to_type(obj['subject']))
    elif 'left' in obj and 'right' in obj and len(obj) == 3:
        return PropCon(obj['prop'], to_type(obj['left']), to_type(obj['right']))
    elif obj['prop'] == 'unknown':
        return PropCon(obj['constructor'], *map(to_type, obj['arguments']))
    else:
        raise NotImplementedError(f"to_prop({obj!r})")


# -----------------------------------------------------------
# Cryptol type schema
# -----------------------------------------------------------

@dataclass
class CryptolTypeSchema:
    variables : OrderedDict[str, CryptolKind]
    propositions : List[CryptolProp]
    body : CryptolType

    def __str__(self) -> str:
        vstr, pstr = "", "()"
        if len(self.variables) > 0:
            vstr = "{" + ", ".join(self.variables.keys()) + "} "
        if len(self.propositions) > 0:
            pstr = "(" + ", ".join(map(str, self.propositions)) + ")"
        return vstr + pstr + " => " + str(self.body)

def to_schema(obj : Any) -> CryptolTypeSchema:
    """Convert a Cryptol JSON type schema to a ``CryptolTypeSchema``."""
    return CryptolTypeSchema(OrderedDict((v['name'], to_kind(v['kind']))
                                         for v in obj['forall']),
                             [to_prop(p) for p in obj['propositions']],
                             to_type(obj['type']))

def to_schema_or_type(obj : Any) -> Union[CryptolTypeSchema, CryptolType]:
    """Convert a Cryptol JSON type schema to a ``CryptolType`` if it has no
    variables or propositions, or to a ``CryptolTypeSchema`` otherwise."""
    if 'forall' in obj and 'propositions' in obj and len(obj['forall']) > 0 and len(obj['propositions']) > 0:
        return to_schema(obj)
    else:
        return to_type(obj['type'])

def argument_types(obj : Union[CryptolTypeSchema, CryptolType]) -> List[CryptolType]:
    """Given a ``CryptolTypeSchema` or ``CryptolType`` of a function, return
    the types of its arguments."""
    if isinstance(obj, CryptolTypeSchema):
        return argument_types(obj.body)
    elif isinstance(obj, Function):
        arg1 = obj.domain
        args = argument_types(obj.range)
        return [arg1] + args
    else:
        return []


# -----------------------------------------------------------
# Cryptol Name Info
# -----------------------------------------------------------

CryptolInfixInfo = TypedDict("CryptolInfixInfo",
    { "associativity": Union[typing_extensions.Literal["left-associative"],
                             typing_extensions.Literal["right-associative"],
                             typing_extensions.Literal["non-associative"]]
    , "level": int
    })

CryptolNameInfo = TypedDict("CryptolNameInfo",
    { "module": str
    , "name": str
    , "type": CryptolTypeSchema
    , "type string": str
    , "documentation": NotRequired[str]
    , "pragmas": NotRequired[List[str]]
    , "parameter": NotRequired[typing.Tuple[()]]
    , "infix": NotRequired[CryptolInfixInfo]
    })

def check_dict(d : Any, required_keys : Dict[str, Any], optional_keys : Dict[str, Any] = {}) -> bool:
    return isinstance(d, dict) and all(k in d for k in required_keys) and \
           all(k in required_keys and isinstance(d[k], required_keys[k]) or
               k in optional_keys and isinstance(d[k], optional_keys[k]) for k in d)

def to_cryptol_name_info(d : Any) -> CryptolNameInfo:
    req_keys = {"module": str, "name": str, "type": Dict, "type string": str}
    opt_keys = {"documentation": str, "pragmas": List, "parameter": List, "infix": Dict}
    infix_req_keys = {"associativity": str, "level": int}
    if check_dict(d, req_keys, opt_keys) and ("infix" not in d or check_dict(d["infix"], infix_req_keys)):
        d["type"] = to_schema(d["type"])
        if "parameter" in d: d["parameter"] = ()
        # the calls to check_dict and the above ensure this cast is OK
        return cast(CryptolNameInfo, d)
    else:
        raise ValueError("Cryptol name info is malformed: " + str(d))


# -----------------------------------------------------------
# Cryptol Module Info
# -----------------------------------------------------------

CryptolFocusedModuleInfo = TypedDict("CryptolFocusedModuleInfo",
    { "module": str
    , "parameterized": bool
    })

CryptolNoModuleInfo = TypedDict("CryptolNoModuleInfo",
    { "module": None
    })

CryptolModuleInfo = Union[CryptolFocusedModuleInfo, CryptolNoModuleInfo]

def to_cryptol_module_info(d : Any) -> CryptolModuleInfo:
    if check_dict(d, {"module": str, "parameterized": bool}):
        # the call to check_dict ensures this cast is OK
        return cast(CryptolFocusedModuleInfo, d)
    elif check_dict(d, {"module": type(None)}):
        # the call to check_dict ensures this cast is OK
        return cast(CryptolNoModuleInfo, d)
    else:
        raise ValueError("Cryptol module info is malformed: " + str(d))

