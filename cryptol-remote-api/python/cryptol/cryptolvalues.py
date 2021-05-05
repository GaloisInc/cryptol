from __future__ import annotations

from math import ceil, floor, trunc
from abc import ABCMeta, abstractmethod
from collections.abc import Iterable
import base64
from typing import Any, Callable, List, NoReturn, Optional, Union, Tuple, Dict, TypeVar
from typing_extensions import Literal
from dataclasses import dataclass
from math import gcd

from . import cryptoltypes
from .bitvector import BV
from .intmod import IntMod

A = TypeVar('A')

class CryValueError(ValueError):
    pass


def cryQ(s : str) -> CryQuoted:
    return CryQuoted(s)

class CryQuoted:
    def __init__(self, s : str) -> None:
        self.value = s

    def __repr__(self) -> str:
        return f'CryQuoted({repr(self.value)})'

    def __str__(self) -> str:
        """Return a string representation as Cryptol syntax."""
        return f'({self.value})'

    # some private functions useful when defining operators

    def __binop(self, op : str, other : Any) -> CryQuoted:
        if isinstance(other, CryQuoted):
            return CryQuoted(f'{self} {op} {other}')
        try:
            otherCry = to_cryptol_value(other)
            return CryQuoted(f'{self} {op} {otherCry}')
        except CryValueError:
            return NotImplemented
    def __rbinop(self, op : str, other : Any) -> CryQuoted:
        if isinstance(other, CryQuoted):
            return CryQuoted(f'{other} {op} {self}')
        try:
            otherCry = to_cryptol_value(other)
            return CryQuoted(f'{otherCry} {op} {self}')
        except CryValueError:
            return NotImplemented

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryQuoted:
        return self.__binop("==", other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : Any) -> CryQuoted:
        return self.__binop("<", other)
    def __le__(self, other : Any) -> CryQuoted:
        return self.__binop("<=", other)
    def __gt__(self, other : Any) -> CryQuoted:
        return self.__binop(">", other)
    def __ge__(self, other : Any) -> CryQuoted:
        return self.__binop(">=", other)

    # operators from the Cryptol `Logic` typeclass

    def __invert__(self) -> CryQuoted:
        return CryQuoted(f'~ {self}')
    def __and__(self, other : Any) -> CryQuoted:
        return self.__binop("&&", other)
    def __rand__(self, other : Any) -> CryQuoted:
        return self.__rbinop("&&", other)
    def __or__(self, other : Any) -> CryQuoted:
        return self.__binop("||", other)
    def __ror__(self, other : Any) -> CryQuoted:
        return self.__rbinop("||", other)
    def __xor__(self, other : Any) -> CryQuoted:
        return self.__binop("^", other)
    def __rxor__(self, other : Any) -> CryQuoted:
        return self.__rbinop("^", other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CryQuoted:
        return CryQuoted(self.value)
    def __neg__(self) -> CryQuoted:
        return CryQuoted(f'- {self}')
    def __add__(self, other : Any) -> CryQuoted:
        return self.__binop("+", other)
    def __radd__(self, other : Any) -> CryQuoted:
        return self.__rbinop("+", other)
    def __sub__(self, other : Any) -> CryQuoted:
        return self.__binop("-", other)
    def __rsub__(self, other : Any) -> CryQuoted:
        return self.__rbinop("-", other)
    def __mul__(self, other : Any) -> CryQuoted:
        return self.__binop("*", other)
    def __rmul__(self, other : Any) -> CryQuoted:
        return self.__rbinop("*", other)
    def __pow__(self, other : Any) -> CryQuoted:
        return self.__binop("^^", other)
    def __rpow__(self, other : Any) -> CryQuoted:
        return self.__rbinop("^^", other)

    # operators from the Cryptol `Integral` typeclass
    
    def __floordiv__(self, other : Any) -> CryQuoted:
        return self.__binop("/", other)
    def __rfloordiv__(self, other : Any) -> CryQuoted:
        return self.__rbinop("/", other)
    def __mod__(self, other : Any) -> CryQuoted:
        return self.__binop("%", other)
    def __rmod__(self, other : Any) -> CryQuoted:
        return self.__rbinop("%", other)

    # operators from the Cryptol `Field` typeclass

    def __truediv__(self, other : Any) -> CryQuoted:
        return self.__binop("/.", other)
    def __rtruediv__(self, other : Any) -> CryQuoted:
        return self.__rbinop("/.", other)

    # operators on Cryptol sequences

    def __len__(self) -> CryQuoted:
        return CryQuoted(f'length {self}')
    def __getitem__(self, other : Any) -> CryQuoted:
        return self.__binop("@", other)
    def __lshift__(self, other : Any) -> CryQuoted:
        return self.__binop("<<", other)
    def __rlshift__(self, other : Any) -> CryQuoted:
        return self.__rbinop("<<", other)
    def __rshift__(self, other : Any) -> CryQuoted:
        return self.__binop(">>", other)
    def __rrshift__(self, other : Any) -> CryQuoted:
        return self.__rbinop(">>", other)

    # conversions

    def __bool__(self) -> bool:
        raise CryValueError("quoted Cryptol does not have a value!")
    def __int__(self) -> int:
        raise CryValueError("quoted Cryptol does not have a value!")
    def __float__(self) -> float:
        raise CryValueError("quoted Cryptol does not have a value!")
    def __index__(self) -> int:
        raise CryValueError("quoted Cryptol does not have a value!")


    
class CryValue(metaclass=ABCMeta):
    """The canonical representation of a Cryptol value.
    The class's `__str__` method converts the value into type-annotated Cryptol syntax."""
    
    @abstractmethod
    def cryptol_term(self) -> str:
        """The Cryptol syntax for this value."""
        pass

    @abstractmethod
    def cryptol_type(self) -> cryptoltypes.CryptolType:
        """The Cryptol type of this value."""
        pass

    def __str__(self) -> str:
        """Return a string representation of this value as it would appear as an annotated Cryptol term."""
        return f'({self.cryptol_term()} : {self.cryptol_type()})'

    @staticmethod
    @abstractmethod
    def from_python(value : Any) -> CryValue:
        """Convert a python value to a particular type of Cryptol value,
           raising a ``CryValueError`` if there is no unambigous mapping."""
        pass


class CryBit(CryValue):
    """A Cryptol boolean value."""
    value: bool
    def __init__(self, value : Union[bool,int]) -> None:
        if isinstance(value, bool):
            self.value = value
        elif isinstance(value, int) and (value == 0 or value == 1):
            self.value = bool(value)
        else:
            raise CryValueError(f'Only a bool, `0`, or `1` can be interpreted as a CryBit, got {value!r}')

    def __repr__(self) -> str:
        return f'CryBit({self.value!r})'

    def cryptol_term(self) -> str:
        return "True" if self.value else "False"

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Bit()

    @staticmethod
    def from_python(value : Any) -> CryBit:
        if isinstance(value, CryBit):
            return value
        else:
            return CryBit(value)
    
    # some private functions useful when defining operators
    
    def __binop(self, op : Callable[[bool,bool], A], other : Any) -> A:
        try:
            otherCry = CryBit.from_python(other)
        except CryValueError:
            return NotImplemented
        return op(self.value, otherCry.value)
    def __rbinop(self, op : Callable[[bool,bool], A], other : Any) -> A:
        return self.__binop(lambda s,o: op(o,s), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s == o), other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s < o), other)
    def __le__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s <= o), other)
    def __gt__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s > o), other)
    def __ge__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s >= o), other)
    
    # operators from the Cryptol `Logic` typeclass

    def __invert__(self) -> CryBit:
        return CryBit(~self.value)
    def __and__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s & o), other)
    def __rand__(self, other : Union[bool,int]) -> CryBit:
        return self.__rbinop(lambda o,s: CryBit(o & s), other)
    def __or__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s | o), other)
    def __ror__(self, other : Union[bool,int]) -> CryBit:
        return self.__rbinop(lambda o,s: CryBit(o | s), other)
    def __xor__(self, other : Union[CryBit,bool,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s ^ o), other)
    def __rxor__(self, other : Union[bool,int]) -> CryBit:
        return self.__rbinop(lambda o,s: CryBit(o ^ s), other)

    # conversions

    def __bool__(self) -> bool:
        return self.value

    def __int__(self) -> int:
        return int(self.value)

    def __float__(self) -> float:
        return float(self.value)

    def __index__(self) -> int:
        return 1 if self.value else 0


class CryInt(CryValue):
    """An (unbounded) Cryptol integer value."""
    value: int
    def __init__(self, value : int) -> None:
        if isinstance(value, int):
            self.value = value
        else:
            raise CryValueError(f'Only an int can be interpreted as a CryInt, got {value!r}')

    def __repr__(self) -> str:
        return f'CryInt({self.value!r})'

    def cryptol_term(self) -> str:
        return str(self.value)

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Integer()

    @staticmethod
    def from_python(value : Union[CryInt,int]) -> CryInt:
        if isinstance(value, CryInt):
            return value
        else:
            return CryInt(value)

    # some private functions useful when defining operators

    def __binop(self, op : Callable[[int,int], A], other : Any) -> A:
        try:
            otherCry = CryInt.from_python(other)
        except CryValueError:
            return NotImplemented
        return op(self.value, otherCry.value)
    def __rbinop(self, op : Callable[[int,int], A], other : Any) -> A:
        return self.__binop(lambda s,o: op(o,s), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s == o), other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : Union[CryInt,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s < o), other)
    def __le__(self, other : Union[CryInt,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s <= o), other)
    def __gt__(self, other : Union[CryInt,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s > o), other)
    def __ge__(self, other : Union[CryInt,int]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s >= o), other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CryInt:
        return CryInt(self.value)
    def __neg__(self) -> CryInt:
        return CryInt(-self.value)
    def __add__(self, other : Union[CryInt,int]) -> CryInt:
        return self.__binop(lambda s,o: CryInt(s + o), other)
    def __radd__(self, other : int) -> CryInt:
        return self.__rbinop(lambda o,s: CryInt(o + s), other)
    def __sub__(self, other : Union[CryInt,int]) -> CryInt:
        return self.__binop(lambda s,o: CryInt(s - o), other)
    def __rsub__(self, other : int) -> CryInt:
        return self.__rbinop(lambda o,s: CryInt(o - s), other)
    def __mul__(self, other : Union[CryInt,int]) -> CryInt:
        return self.__binop(lambda s,o: CryInt(s * o), other)
    def __rmul__(self, other : int) -> CryInt:
        return self.__rbinop(lambda o,s: CryInt(o * s), other)
    def __pow__(self, other : Any) -> CryInt:
        return CryInt(self.value ** int(other))

    # operators from the Cryptol `Integral` typeclass

    def __floordiv__(self, other : Union[CryInt,int]) -> CryInt:
        return self.__binop(lambda s,o: CryInt(s // o), other)
    def __rfloordiv__(self, other : int) -> CryInt:
        return self.__rbinop(lambda o,s: CryInt(o // s), other)
    def __mod__(self, other : Union[CryInt,int]) -> CryInt:
        return self.__binop(lambda s,o: CryInt(s % o), other)
    def __rmod__(self, other : int) -> CryInt:
        return self.__rbinop(lambda o,s: CryInt(o % s), other)

    # conversions

    def __bool__(self) -> bool:
        return bool(self.value)

    def __int__(self) -> int:
        return self.value

    def __float__(self) -> float:
        return float(self.value)

    def __index__(self) -> int:
        return self.value


class CryIntMod(CryValue):
    """A Cryptol integer value modulo ``n`` where ``n > 0``."""
    value: IntMod
    def __init__(self, value : Union[IntMod,int], n : Optional[int] = None) -> None:
        if isinstance(value, int) and n is not None:
            self.value = IntMod(value, n)
        elif isinstance(value, IntMod) and ((n is None) or n == value.modulus()):
            self.value = value
        else:
            raise CryValueError(f'`CryIntMod` expects either an `IntMod` or an integer modulus and value, got {value!r}')
    
    def __repr__(self) -> str:
        return f'CryIntMod({self.value.value()!r}, {self.value.modulus()!r})'

    def cryptol_term(self) -> str:
        return str(self.value.value())

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Z(cryptoltypes.Num(self.value.modulus()))

    @staticmethod
    def from_python(value : Union[CryIntMod,IntMod]) -> CryIntMod:
        if isinstance(value, CryIntMod):
            return value
        elif isinstance(value, IntMod):
            return CryIntMod(value)
        else:
            raise CryValueError(f'Only an `IntMod` can be interpreted as a CryIntMod, got {value!r}')

    # some private functions useful when defining operators

    def __binop(self, op : Callable[[IntMod,IntMod], A], other : Any) -> A:
        try:
            otherCry = CryIntMod.from_python(other)
        except CryValueError:
            return NotImplemented
        return op(self.value, otherCry.value)
    def __rbinop(self, op : Callable[[IntMod,IntMod], A], other : Any) -> A:
        return self.__binop(lambda s,o: op(o,s), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s == o), other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CryIntMod:
        return CryIntMod(self.value)
    def __neg__(self) -> CryIntMod:
        return CryIntMod(-self.value)
    def __add__(self, other : Union[CryIntMod,int]) -> CryIntMod:
        return self.__binop(lambda s,o: CryIntMod(s + o), other)
    def __radd__(self, other : int) -> CryIntMod:
        return self.__rbinop(lambda o,s: CryIntMod(o + s), other)
    def __sub__(self, other : Union[CryIntMod,int]) -> CryIntMod:
        return self.__binop(lambda s,o: CryIntMod(s - o), other)
    def __rsub__(self, other : int) -> CryIntMod:
        return self.__rbinop(lambda o,s: CryIntMod(o - s), other)
    def __mul__(self, other : Union[CryIntMod,int]) -> CryIntMod:
        return self.__binop(lambda s,o: CryIntMod(s * o), other)
    def __rmul__(self, other : int) -> CryIntMod:
        return self.__rbinop(lambda o,s: CryIntMod(o * s), other)
    def __pow__(self, other : Any) -> CryIntMod:
        return CryIntMod(self.value ** int(other))
    
    # conversions

    def __bool__(self) -> bool:
        return bool(self.value.value())


class CryRatio(CryValue):
    """A (reduced) Cryptol rational number (``numerator / denominator``) value."""
    numerator: int
    denominator: int
    def __init__(self, numerator : int, denominator : Optional[int] = None) -> None:
        if not isinstance(numerator, int):
            raise CryValueError(f'`CryRatio` expects `numerator` to be an integer, but got {numerator!r}')
        if denominator is None:
            self.numerator = numerator
            self.denominator = 1
        else:
            if not isinstance(denominator, int) or denominator == 0:
                raise CryValueError(f'`CryRatio` expects `denominator` to be a non-zero integer, but got {denominator!r}')
            if numerator < 0 and denominator < 0 or numerator > 0 and denominator > 0:
                sign = 1
            else:
                sign = -1
            d = gcd(numerator, denominator)
            self.numerator = (sign * abs(numerator)) // d
            self.denominator = abs(denominator) // d

    def __repr__(self) -> str:
        return f'CryRatio({self.numerator!r}, {self.denominator!r})'

    def cryptol_term(self) -> str:
        return f'ratio {self.numerator} {self.denominator}'

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Rational()

    @staticmethod
    def from_python(value : CryRatio) -> CryRatio:
        if isinstance(value, CryRatio):
            return value
        else:
            raise CryValueError(f'Cannot interpret {value!r} as a CryRatio')

    # some private functions useful when defining operators

    def __binop(self, op : Callable[[int,int,int,int], A], other : Any) -> A:
        try:
            otherCry = CryRatio.from_python(other)
        except CryValueError:
            return NotImplemented
        return op(self.numerator, self.denominator,
                  otherCry.numerator, otherCry.denominator)
    def __rbinop(self, op : Callable[[int,int,int,int], A], other : Any) -> A:
        return self.__binop(lambda sn,sd,on,od: op(on,od,sn,sd), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda sn,sd,on,od: CryBit(sn * od == on * sd), other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : CryRatio) -> CryBit:
        return self.__binop(lambda sn,sd,on,od: CryBit(sn * od < on * sd), other)
    def __le__(self, other : CryRatio) -> CryBit:
        return self.__binop(lambda sn,sd,on,od: CryBit(sn * od <= on * sd), other)
    def __gt__(self, other : CryRatio) -> CryBit:
        return self.__binop(lambda sn,sd,on,od: CryBit(sn * od > on * sd), other)
    def __ge__(self, other : CryRatio) -> CryBit:
        return self.__binop(lambda sn,sd,on,od: CryBit(sn * od >= on * sd), other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CryRatio:
        return CryRatio(self.numerator, self.denominator)
    def __neg__(self) -> CryRatio:
        return CryRatio(-self.numerator, self.denominator)
    def __add__(self, other : CryRatio) -> CryRatio:
        return self.__binop(lambda sn,sd,on,od: CryRatio(sn * od + on * sd, sd * od), other)
    def __sub__(self, other : CryRatio) -> CryRatio:
        return self.__binop(lambda sn,sd,on,od: CryRatio(sn * od - on * sd, sd * od), other)
    def __mul__(self, other : CryRatio) -> CryRatio:
        return self.__binop(lambda sn,sd,on,od: CryRatio(sn * on, sd * od), other)
    def __pow__(self, other : Any) -> CryRatio:
        return CryRatio(self.numerator ** int(other),
                        self.denominator ** int(other))

    # operators from the Cryptol `Field` typeclass

    def __div__(self, other : CryRatio) -> CryRatio:
        return self.__binop(lambda sn,sd,on,od: CryRatio(sn * od, sd * on), other)
    
    # operators from the Cryptol `Round` typeclass

    def __ceil__(self) -> CryInt:
        return CryInt(ceil(float(self)))
    def __floor__(self) -> CryInt:
        return CryInt(floor(float(self)))
    def __trunc__(self) -> CryInt:
        return CryInt(trunc(float(self)))

    # conversions

    def __bool__(self) -> bool:
        return bool(self.numerator)

    def __float__(self) -> float:
        return float(self.numerator) / float(self.denominator)


class CryTuple(CryValue):
    """An n-ary Cryptol tuple (i.e., an ordered heterogeneous collection of values)."""
    elements: List[CryValue]
    def __init__(self, *elements : Any) -> None:
        self.elements = [to_cryptol_value(v) for v in elements]

    def __repr__(self) -> str:
        return 'CryTuple(' + ", ".join(map(repr, self.elements)) + ')'

    def cryptol_term(self) -> str:
        return '(' + ', '.join(e.cryptol_term() for e in self.elements) + ')'

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Tuple(*[e.cryptol_type() for e in self.elements])

    @staticmethod
    def from_python(value : Union[CryTuple,Tuple]) -> CryTuple:
        if isinstance(value, CryTuple):
            return value
        elif isinstance(value, tuple):
            return CryTuple(*value)
        else:
            raise CryValueError(f'Only a tuple can be interpreted as a CryTuple, got {value!r}')

    # some private functions useful when defining operators

    def __binop(self, op : Callable[[List[Any],List[Any]], A], other : Any) -> A:
        try:
            otherCry = CryTuple.from_python(other)
        except CryValueError:
            return NotImplemented
        if len(self.elements) != len(otherCry.elements):
            raise ValueError(f"CryTuples have mismatched lengths: {self!r} and {other!r}")
        return op(self.elements, otherCry.elements)
    def __rbinop(self, op : Callable[[List[CryValue],List[CryValue]], A], other : Any) -> A:
        return self.__binop(lambda s,o: op(o,s), other)

    def __unopOnElts(self, op : Callable[[Any], Any]) -> CryTuple:
        return CryTuple(*(op(si) for si in self.elements))

    def __binopOnElts(self, op : Callable[[Any,Any], Any], other : Any) -> CryTuple:
        def opOnWhole(s : List[Any], o : List[Any]) -> CryTuple:
            return CryTuple(*(op(si,oi) for [si,oi] in zip(s,o)))
        return self.__binop(opOnWhole, other)
    def __rbinopOnElts(self, op : Callable[[Any,Any], Any], other : Any) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: op(oi,si), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s == o), other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : Union[CryTuple,Tuple]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s < o), other)
    def __le__(self, other : Union[CryTuple,Tuple]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s <= o), other)
    def __gt__(self, other : Union[CryTuple,Tuple]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s > o), other)
    def __ge__(self, other : Union[CryTuple,Tuple]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s >= o), other)

    # operators from the Cryptol `Logic` typeclass

    def __invert__(self) -> CryTuple:
        return self.__unopOnElts(lambda si: ~si)
    def __and__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si & oi, other)
    def __rand__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi & si, other)
    def __or__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si | oi, other)
    def __ror__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi | si, other)
    def __xor__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si ^ oi, other)
    def __rxor__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi ^ si, other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CryTuple:
        return self.__unopOnElts(lambda si: +si)
    def __neg__(self) -> CryTuple:
        return self.__unopOnElts(lambda si: -si)
    def __add__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si + oi, other)
    def __radd__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi + si, other)
    def __sub__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si - oi, other)
    def __rsub__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi - si, other)
    def __mul__(self, other : Union[CryTuple,Tuple]) -> CryTuple:
        return self.__binopOnElts(lambda si,oi: si * oi, other)
    def __rmul__(self, other : Tuple) -> CryTuple:
        return self.__rbinopOnElts(lambda oi,si: oi * si, other)
    def __pow__(self, other : Any) -> CryTuple:
        return self.__unopOnElts(lambda si: si ** int(other))

    # container operators

    def __len__(self) -> int:
        return len(self.elements)

    def __getitem__(self, key : int) -> CryValue:
        return self.elements[key]


class CrySeq(CryValue):
    """A Cryptol sequence (i.e., an ordered homogeneous collection of values). We represent these
       here as a bitvector (if the element type is `Bit()`), a list of values, or a string (if the
       element type is ``[8]`` and a string is given to `__init__`)."""
    value: Union[List[CryValue], BV, str]
    element_type: cryptoltypes.CryptolType

    def __init__(self, value : Union[List[CryValue],BV,str], element_type : Optional[cryptoltypes.CryptolType] = None) -> None:
        if isinstance(value, list):
            valueCry = [to_cryptol_value(e) for e in value]
            if element_type is not None:
                self.element_type = element_type
            elif len(valueCry) > 0:
                self.element_type = valueCry[0].cryptol_type()
            else:
                raise ValueError("`CrySeq` must be have a specified `element_type` if given an empty list.")
            if any(v.cryptol_type() != self.element_type for v in valueCry):
                raise ValueError(f"All values in a `CrySeq` must have the same type, got {valueCry!r}")
            if self.element_type == cryptoltypes.Bit():
                bitStr = "".join("1" if v else "0" for v in valueCry)
                self.value = BV(value=int(bitStr, 2), size=len(value))
            else:
                self.value = [to_cryptol_value(e) for e in value]
        elif isinstance(value, BV):
            self.value = value
            self.element_type = cryptoltypes.Bit()
            if element_type is not None and element_type != self.element_type:
                raise ValueError(f"`CrySeq` given a bitvector but not `element_type={self.element_type!r}`")
        elif isinstance(value, str):
            self.value = value
            self.element_type = cryptoltypes.Sequence(cryptoltypes.Num(8),
                                                      cryptoltypes.Bit())
            if element_type is not None and element_type != self.element_type:
                raise ValueError(f"`CrySeq` given a string but not `element_type={self.element_type!r}`")
        else:
            raise CryValueError("`CrySeq` expects a list, BV, or str")

    def __repr__(self) -> str:
        if isinstance(self.value, list):
            return f'CrySeq({self.value!r}, {self.element_type!r})'
        else:
            return f'CrySeq({self.value!r})'

    def cryptol_term(self) -> str:
        if isinstance(self.value, list):
            return "[" + ", ".join(e.cryptol_term() for e in self.value) + "]"
        elif isinstance(self.value, BV):
            return self.value.hex()
        elif isinstance(self.value, str):
            return repr(self.value)

    def cryptol_type(self) -> cryptoltypes.CryptolType:
        return cryptoltypes.Sequence(cryptoltypes.Num(len(self.value)),
                                     self.element_type)

    @staticmethod
    def from_python(value : Union[CrySeq,List[CryValue],BV,str],
                    *, element_type : Optional[cryptoltypes.CryptolType] = None) -> CrySeq:
        if isinstance(value, CrySeq):
            if value.element_type != element_type:
                raise ValueError(f"`Expected a `CrySeq` with `element_type={element_type}`, got {value!r}")
            return value
        else:
            return CrySeq(value, element_type=element_type)

    def valueAsBVOrList(self) -> Union[List[CryValue],BV]:
        """The value of this sequence, unpacking it if it is represented as a string"""
        if isinstance(self.value, str):
            return [ CryBV(8,b) for b in bytes(self.value, "ascii") ]
        else:
            return self.value

    def valueAsList(self) -> List[CryValue]:
        """The value of this sequence, unpacking it if it is represented as a string or bitvector"""
        v = self.valueAsBVOrList()
        if isinstance(v, BV):
            return [ CryBit(v[i]) for i in reversed(range(0,len(v))) ]
        else:
            return v

    # some private functions useful when defining operators

    def __binop(self, op : Callable[[Any,Any], A], other : Any) -> A:
        try:
            otherCry = CrySeq.from_python(other, element_type=self.element_type)
        except CryValueError:
            return NotImplemented
        s = self.valueAsBVOrList()
        o = otherCry.valueAsBVOrList()
        if len(s) != len(o):
            raise ValueError(f"CrySeqs have mismatched lengths: {self!r} and {other!r}")
        return op(s,o)
    def __rbinop(self, op : Callable[[Any,Any], A], other : Any) -> A:
        return self.__binop(lambda s,o: op(o,s), other)

    def __unopOnElts(self, op : Callable[[Any], Any]) -> CrySeq:
        s = self.valueAsBVOrList()
        if isinstance(s, BV):
            return CrySeq(op(s), element_type=self.element_type)
        else:
            return CrySeq([op(si) for si in s], element_type=self.element_type)

    def __binopOnElts(self, op : Callable[[Any,Any], Any], other : Any) -> CrySeq:
        def opOnWhole(s : Any, o : Any) -> CrySeq:
            if isinstance(s, BV):
                return CrySeq(op(s, o), element_type=self.element_type)
            else:
                return CrySeq([op(si,oi) for [si,oi] in zip(s,o)],
                              element_type=self.element_type)
        return self.__binop(opOnWhole, other)
    def __rbinopOnElts(self, op : Callable[[Any,Any], Any], other : Any) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: op(oi,si), other)

    # operators from the Cryptol `Eq` typeclass

    # FIXME mypy complains about this return type
    def __eq__(self, other : Any) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s == o), other)

    # operators from the Cryptol `Cmp` typeclass

    def __lt__(self, other : Union[CrySeq,List[Any]]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s < o), other)
    def __le__(self, other : Union[CrySeq,List[Any]]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s <= o), other)
    def __gt__(self, other : Union[CrySeq,List[Any]]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s > o), other)
    def __ge__(self, other : Union[CrySeq,List[Any]]) -> CryBit:
        return self.__binop(lambda s,o: CryBit(s >= o), other)

    # operators from the Cryptol `Logic` typeclass

    def __invert__(self) -> CrySeq:
        return self.__unopOnElts(lambda si: ~si)
    def __and__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si & oi, other)
    def __rand__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi & si, other)
    def __or__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si | oi, other)
    def __ror__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi | si, other)
    def __xor__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si ^ oi, other)
    def __rxor__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi ^ si, other)

    # operators from the Cryptol `Ring` typeclass

    def __pos__(self) -> CrySeq:
        return self.__unopOnElts(lambda si: +si)
    def __neg__(self) -> CrySeq:
        return self.__unopOnElts(lambda si: -si)
    def __add__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si + oi, other)
    def __radd__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi + si, other)
    def __sub__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si - oi, other)
    def __rsub__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi - si, other)
    def __mul__(self, other : Union[CrySeq,List[Any]]) -> CrySeq:
        return self.__binopOnElts(lambda si,oi: si * oi, other)
    def __rmul__(self, other : List[Any]) -> CrySeq:
        return self.__rbinopOnElts(lambda oi,si: oi * si, other)
    def __pow__(self, other : Union[CryInt,int]) -> CrySeq:
        try:
            otherCry = CryInt.from_python(other)
        except CryValueError:
            return NotImplemented
        return self.__unopOnElts(lambda si: si ** otherCry.value)

    # operators on Cryptol sequences

    def __len__(self) -> int:
        return len(self.value)

    def __getitem__(self, key : int) -> CryValue:
        return self.valueAsList()[key]

    def __lshift__(self, other : Any) -> CrySeq:
        v = self.valueAsBVOrList()
        n = int(other)
        if n < 0:
            raise ValueError(f'Cannot left shift a negative amount (i.e, {n!r}).')
        if isinstance(v, BV):
            return CryBV(v.size(), (v.value() << n) % (2 ** v.size()))
        else:
            z = cryptol_zero(self.element_type)
            return CrySeq(v[n:] + [z]*n, element_type=self.element_type)

    def __rshift__(self, other : Any) -> CrySeq:
        v = self.valueAsBVOrList()
        n = int(other)
        if n < 0:
            raise ValueError(f'Cannot right shift a negative amount (i.e, {n!r}).')
        if isinstance(v, BV):
            return CryBV(v.size(), (v.value() >> n) % (2 ** v.size()))
        else:
            z = cryptol_zero(self.element_type)
            return CrySeq([z]*n + v[0:-n], element_type=self.element_type)

    # conversions

    def __bool__(self) -> int:
        if isinstance(self.value, BV):
            return bool(self.value.value())
        else:
            return bool(len(self.value))

    def __int__(self) -> int:
        if isinstance(self.value, BV):
            return self.value.value()
        else:
            raise ValueError("non-bitvector `CrySeq` cannot be converted to an integer")

    def __float__(self) -> float:
        return float(int(self))

    def __index__(self) -> int:
        return int(self)

def CryBV(size : Union[int, BV], value : Optional[int] = None) -> CrySeq:
    """A synonym for `CrySeq(BV(size, value))`."""
    return CrySeq(BV(size, value))



def to_cryptol_value(value : Any) -> CryValue:
    """Convert a python value to a ``CryValue``, raising a ``ValueError`` if there is no unambigous mapping."""
    if isinstance(value, CryValue):
        return value
    elif isinstance(value, bool):
        return CryBit(value)
    elif isinstance(value, int):
        return CryInt(value)
    elif isinstance(value, IntMod):
        return CryIntMod(value)
    elif isinstance(value, tuple):
        return CryTuple(*(to_cryptol_value(v) for v in value))
    elif isinstance(value, BV) or isinstance(value, str):
        return CrySeq(value)
    elif isinstance(value, Iterable):
        elements = [to_cryptol_value(v) for v in value]
        if elements == []:
            raise ValueError(f'An empty sequence does not have an unambigous mapping to a CryValue')
        else:
            return CrySeq(elements)
    else:
        raise ValueError(f'There is no unambiguous mapping from {value!r} to a CryValue')

def cryptol_zero(type : cryptoltypes.CryptolType) -> CryValue:
    """Return the Cryptol `zero` value of the given Cryptol type."""
    if isinstance(type, cryptoltypes.Bit):
        return CryBit(0)
    elif isinstance(type, cryptoltypes.Integer):
        return CryInt(0)
    elif isinstance(type, cryptoltypes.Z):
        if not isinstance(type.modulus, cryptoltypes.Num):
            raise ValueError(f'Z type given to `cryptol_zero` does not have `Num` modulus, got {type.modulus!r}')
        return CryIntMod(0, type.modulus.number)
    elif isinstance(type, cryptoltypes.Rational):
        return CryRatio(0)
    elif isinstance(type, cryptoltypes.Tuple):
        return CryTuple(*(cryptol_zero(etype) for etype in type.types))
    elif isinstance(type, cryptoltypes.Sequence):
        if not isinstance(type.length, cryptoltypes.Num):
            raise ValueError(f'Sequence type given to `cryptol_zero` does not have `Num` length, got {type.length!r}')
        return CrySeq([cryptol_zero(type.contents)] * type.length.number,
                      element_type=type.contents)
    else:
        raise ValueError(f'Type given to `cryptol_zero` has no zero, got {type!r}')
