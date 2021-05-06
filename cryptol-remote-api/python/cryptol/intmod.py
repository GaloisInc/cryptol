
from __future__ import annotations
from typing import Any, Union

class IntMod:
    """A class representing a cryptol modular integer (i.e. a value of type  ``Z n``).

    ``IntMod(value : int, n : int)`` will create a modular integer with modulus ``n`` and value
    ``value % n`` (N.B., ``0 <= abs(value) < n`` must evaluate to ``True`` or an error will be raised).

    N.B., the ``n`` and ``value`` arguments can be passed positionally or by name:

    ``IntMod(-1,12) == IntMod(value=-1, n=12) == IntMod(n=12, value=-1)``
    """
    __modulus  : int
    __value : int
    
    def __init__(self, value : int, n : int):
        """Initialize a modular integer from a modulus and value."""
        if not isinstance(n, int) or n <= 0:
            raise ValueError(f'`IntMod` expects `n` to be a strictly positive integer, but was given {n!r}.')
        if not isinstance(value, int):
            raise ValueError(f'`IntMod` expects `value` to be an integer, but got {value!r}')
        if abs(value) >= n:
          raise ValueError(f'`IntMod` expects `n` to satisfy |value| < n, but got |{value!r}| >= {n!r}')
        self.__modulus = n
        self.__value = value % self.__modulus
    
    def __repr__(self) -> str:
        return f"IntMod({self.__value!r}, {self.__modulus!r})"
    
    def modulus(self) -> int:
        """Modulus of the modular integer."""
        return self.__modulus
        
    def value(self) -> int:
        """Positive value of the modular integer"""
        return self.__value
        
    def __eq__(self, other : Any) -> bool:
        """Returns ``True`` if ``other`` is also an ``IntMod`` with the same modulus, else returns ``False``."""
        if isinstance(other, IntMod):
            return self.__value == other.__value and \
                   self.__modulus == other.__modulus
        else:
            return False

    def __pos__(self) -> 'IntMod':
        return IntMod(self.__value, self.__modulus)

    def __neg__(self) -> 'IntMod':
        return IntMod((-self.__value) % self.__modulus, self.__modulus)

    def __add__(self, other : Union[int, 'IntMod']) -> 'IntMod':
        """Addition bewteen ``IntMod``s of the same modulus or bewteen a ``IntMod``
           and an integer whose absolute value is less than the modulus"""
        if isinstance(other, IntMod):
            if self.__modulus == other.__modulus:
                return IntMod((self.__value + other.__value) % self.__modulus, self.__modulus)
            else:
                raise ValueError(self.__unequal_modulus_op_error_msg("+", other))
        elif isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value + other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot add {self!r} with {other!r}.')
    
    def __radd__(self, other : int) -> 'IntMod':
        if isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value + other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot add {self!r} with {other!r}.')

    def __sub__(self, other : Union[int, 'IntMod']) -> 'IntMod':
        """Subtraction bewteen ``IntMod``s of the same modulus or bewteen a ``IntMod``
           and an integer whose absolute value is less than the modulus"""
        if isinstance(other, IntMod):
            if self.__modulus == other.__modulus:
                return IntMod((self.__value - other.__value) % self.__modulus, self.__modulus)
            else:
                raise ValueError(self.__unequal_modulus_op_error_msg("-", other))
        elif isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value - other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot subtract {self!r} with {other!r}.')
    
    def __rsub__(self, other : int) -> 'IntMod':
        if isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value - other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot subtract {self!r} with {other!r}.')

    def __mul__(self, other : Union[int, 'IntMod']) -> 'IntMod':
        """Multiplication bewteen ``IntMod``s of the same modulus or bewteen a ``IntMod``
           and an integer whose absolute value is less than the modulus"""
        if isinstance(other, IntMod):
            if self.__modulus == other.__modulus:
                return IntMod((self.__value * other.__value) % self.__modulus, self.__modulus)
            else:
                raise ValueError(self.__unequal_modulus_op_error_msg("*", other))
        elif isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value * other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot multiply {self!r} with {other!r}.')
    
    def __rmul__(self, other : int) -> 'IntMod':
        if isinstance(other, int) and abs(other) < self.__modulus:
            return IntMod((self.__value * other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot multiply {self!r} with {other!r}.')

    def __pow__(self, other : int) -> 'IntMod':
        """Raising a modular integer to a positive integer power"""
        if isinstance(other, int) and other >= 0:
            return IntMod((self.__value ** other) % self.__modulus, self.__modulus)
        else:
            raise ValueError(f'Cannot raise {self!r} to the power of {other!r}.')

    def __unequal_modulus_op_error_msg(self, op : str, other : 'IntMod') -> str:
        return f'Operator `{op}` cannot be called on modular integers of unequal moduli {self!r} and {other!r}.'
