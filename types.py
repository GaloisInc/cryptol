from collections import OrderedDict


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

class CryptolType:
    pass

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
        t['value']
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
