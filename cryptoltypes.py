from collections import OrderedDict
import base64
import BitVector


class CryptolCode:
    def __call__(self, other):
        return CryptolApplication(self, other)

class CryptolLiteral(CryptolCode):
    def __init__(self, code):
        self._code = code

    def __to_cryptol__(self, ty):
        return self._code

class CryptolApplication(CryptolCode):
    def __init__(self, rator, *rands):
        self._rator = rator
        self._rands = rands

    def __to_cryptol__(self, ty):
        return {'expression': 'call',
                'function': to_cryptol(self._rator),
                'arguments': [to_cryptol(arg) for arg in self._rands]}


class CryptolArrowKind:
    def __init__(self, dom, ran):
        self.domain = dom
        self.range = ran

    def __repr__(self):
        return f"CryptolArrowKind({self.domain!r}, {self.range!r})"

def to_kind(k):
    if k == "Type": return "Type"
    elif k == "Num": return "Num"
    elif k == "Prop": return "Prop"
    elif k['kind'] == "arrow":
        return CryptolArrowKind(k['from'], k['to'])

class CryptolProp:
    pass

class UnaryProp(CryptolProp):
    def __init__(self, subject):
        self.subject = subject

class Fin(UnaryProp):
    def __repr__(self):
        return f"Fin({self.subject!r})"

def to_cryptol(val, cryptol_type=None):
    if cryptol_type is not None:
        return cryptol_type.from_python(val)
    else:
        return CryptolType().from_python(val)

class CryptolType:
    def from_python(self, val):
        if hasattr(val, '__to_cryptol__'):
            return val.__to_cryptol__(self)
        else:
            return self.convert(val)

    def convert(self, val):
        if isinstance(val, bool):
            return val
        elif val == ():
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
            return {'expression': 'bits',
                    'encoding': 'base64',
                    'width': val.length(),
                    'data': val.pad_from_left(val.length() % 4).get_bitvector_in_hex()}

        else:
            raise TypeError("Unsupported value: " + str(val))

class Var(CryptolType):
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind

    def __repr__(self):
        return f"Var({self.name!r}, {self.kind!r})"



class Function(CryptolType):
    def __init__(self, dom, ran):
        self.domain = dom
        self.range = ran

    def __repr__(self):
        return f"Function({self.domain!r}, {self.range!r})"

class Bitvector(CryptolType):
    def __init__(self, width):
        self.width = width

    def __repr__(self):
        return f"Bitvector({self.width!r})"

    def convert(self, val):
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
        else:
            raise ValueError(f"Not supported as bitvector: {val!r}")

def eval_numeric(t, default):
    if isinstance(t, Num):
        return t.number
    else:
        return default


class Num(CryptolType):
    def __init__(self, number):
        self.number = number

    def __repr__(self):
        return f"Num({self.number!r})"

class Bit(CryptolType):
    def __init__(self):
        pass

    def __repr__(self):
        return f"Bit()"

class Sequence(CryptolType):
    def __init__(self, length, contents):
        self.length = length
        self.contents = contents

    def __repr__(self):
        return f"Sequence({self.length!r}, {self.contents!r})"

class Inf(CryptolType):
    def __repr__(self):
        return f"Inf()"

class Integer(CryptolType):
    def __repr__(self):
        return f"Integer()"

class Z(CryptolType):
    def __init__(self, modulus):
        self.modulus = modulus

    def __repr__(self):
        return f"Z({self.modulus!r})"


class Plus(CryptolType):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} + {self.right})"

    def __repr__(self):
        return f"Plus({self.left!r}, {self.right!r})"

class Minus(CryptolType):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} - {self.right})"

    def __repr__(self):
        return f"Minus({self.left!r}, {self.right!r})"

class Times(CryptolType):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} * {self.right})"

    def __repr__(self):
        return f"Times({self.left!r}, {self.right!r})"


class Tuple(CryptolType):
    def __init__(self, *types):
        self.types = types
    def __repr__(self):
        return "Tuple(" + ", ".join(map(str, types)) + ")"

class Record(CryptolType):
    def __init__(self, fields):
        self.fields = fields

    def __repr__(self):
        return f"Record({self.fields!r})"

def to_type(t):
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
    elif t['type'] == 'tuple':
        return Tuple(*map(to_type, t['contents']))
    elif t['type'] == 'record':
        return Record({k : to_type(t['fields'][k]) for k in t['fields']})
    elif t['type'] == 'Integer':
        return Integer()
    elif t['type'] == 'Z':
        return Z(to_type(t['modulus']))
    else:
        raise NotImplementedError(f"to_type({t!r})")

class CryptolTypeSchema:
    def __init__(self, variables, propositions, body):
        self.variables = variables
        self.propositions = propositions
        self.body = body

    def __repr__(self):
        return f"CryptolTypeSchema({self.variables!r}, {self.propositions!r}, {self.body!r})"

def to_schema(obj):
    return CryptolTypeSchema(OrderedDict((v['name'], to_kind(v['kind']))
                                         for v in obj['forall']),
                             [to_prop(p) for p in obj['propositions']],
                             to_type(obj['type']))

def to_prop(obj):
    if obj['prop'] == 'fin':
        return Fin(to_type(obj['subject']))

def argument_types(obj):
    if isinstance(obj, CryptolTypeSchema):
        return argument_types(obj.body)
    elif isinstance(obj, Function):
        arg1 = obj.domain
        args = argument_types(obj.range)
        return [arg1] + args
    else:
        return []
