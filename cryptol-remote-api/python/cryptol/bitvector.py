
from functools import reduce
from typing import Any, List, Union, Optional, overload
from typing_extensions import Literal
from BitVector import BitVector #type: ignore

ByteOrder = Union[Literal['little'], Literal['big']]


class BV:
    """A class representing a cryptol bit vector (i.e., a sequence of bits).

    ``BV(size : int, value : int)`` will create a ``BV`` of length ``size`` and bits corresponding
    to the unsigned integer representation of ``value`` (N.B., ``0 <= size <= value <= 2 ** size - 1``
    must evaluate to ``True`` or an error will be raised).

    N.B., the ``size`` and ``value`` arguments can be passed positionally or by name:

    ``BV(8,0xff) == BV(size=8, value=0xff) == BV(value=0xff, size=8)``

    ``BV(bv : BitVector)`` will create an equivalent ``BV`` to the given ``BitVector`` value.
    """
    __size  : int
    __value : int

    def __init__(self, size : Union[int, BitVector], value : Optional[int] = None) -> None:
        """Initialize a ``BV`` from a ``BitVector`` or from size and value nonnegative integers."""
        if value is not None:
            if not isinstance(size, int) or size < 0:
                raise ValueError(f'`size` parameter to BV must be a nonnegative integer but was given {size!r}.')
            self.__size = size
            if not isinstance(value, int):
                raise ValueError(f'{value!r} is not an integer value to initilize a bit vector of size {self.__size!r} with.')
            self.__value = value
        elif not isinstance(size, BitVector):
            raise ValueError(f'BV can only be created from a single value when that value is a BitVector, but got {size!r}')
        else:
            self.__size = len(size)
            self.__value = int(size)
        if self.__value < 0 or self.__value.bit_length() > self.__size:
            raise ValueError(f'{self.__value!r} is not representable as an unsigned integer with {self.__size!r} bits.')

    def hex(self) -> str:
        """Return the (padded) hexadecimal string for the unsigned integer this ``BV`` represents.
        
        Note: padding is determined by ``self.size()``, rounding up a single digit
        for widths not evenly divisible by 4."""
        hex_str_width = 2 + (self.__size // 4) + (0 if (self.__size % 4 == 0) else 1)
        return format(self.__value, f'#0{hex_str_width!r}x')

    def __repr__(self) -> str:
        return f"BV({self.__size!r}, {self.hex()})"

    @overload
    def __getitem__(self, key : int) -> bool:
        pass
    @overload
    def __getitem__(self, key : slice) -> 'BV':
        pass
    def __getitem__(self, key : Union[int, slice]) -> Union[bool, 'BV']:
        """``BV`` indexing and slicing.

        :param key: If ``key`` is an integer, ``True`` is returned if the corresponding bit
            is non-zero, else ``False`` is returned. If ``key`` is a ``slice`` (i.e., ``[high:low]``)
            it specifies a sub-``BV`` of ``self`` corresponding to the bits from
            index ``low`` up until (but not including) index ``high``.

        Examples:

        ``BV(8,0b00000010)[0] == False``

        ``BV(8,0b00000010)[1] == True``

        ``BV(8,0b00000010)[4:0] == BV(4,0b0010)``
        """
        if isinstance(key, int):
            if key < 0 or key >= self.__size:
                raise ValueError(f'{key!r} is not a valid index for {self!r}')
            else:
                return (self.__value & (1 << key)) != 0
        if isinstance(key, slice):
            high = key.start
            low = key.stop
            if not isinstance(low, int): raise ValueError(f'Expected BV slice to use non-negative integer indices, but got low index of {low!r}.')
            if low < 0 and low > self.__size: raise ValueError(f'Expected BV slice low index to be >= 0 and <= the BV size (i.e., {self.__size!r}) but got {low!r}.')
            if not isinstance(high, int): raise ValueError(f'Expected BV slice to use non-negative integer indices, but got high index of {high!r}.')
            if low > high: raise ValueError(f'BV slice low index {low!r} is larger than the high index {high!r}.')
            if high > self.__size: raise ValueError(f'BV slice high index {high!r} is larger than the BV size (i.e., {self.__size!r}).')
            if key.step: raise ValueError(f'BV slicing expects a step of None, but found {key.step!r}')
            new_sz = high - low
            return BV(new_sz, (self.__value >> low) & ((2 ** new_sz) - 1))
        else:
            raise ValueError(f'{key!r} is not a valid BV index or slice.')

    def size(self) -> int:
        """Size of the ``BV`` (i.e., the available "bit width")."""
        return self.__size

    def widen(self, n : int) -> 'BV':
        """Returns a "widened" version of ``self``, i.e. ``BV(self.size() + n, self.value())``.

        Args:
            n (int): How many bits wider the returned ``BV`` should be than ``self`` (must be nonnegative).
        """
        if not isinstance(n, int) or n < 0:
            raise ValueError(f'``widen`` expects a nonnegative integer, but got {n!r}')
        else:
            return BV(self.__size + n, self.__value)

    def value(self) -> int:
        """The unsigned integer interpretation of the ``self``."""
        return self.__value

    def __concat_single(self, other : 'BV') -> 'BV':
        if isinstance(other, BV):
            return BV(self.__size + other.__size, (self.__value << other.__size) + other.__value)
        else:
            raise ValueError(f'Cannot concat BV with {other!r}')

    def concat(self, *others : 'BV') -> 'BV':
        """Concatenate the given ``BV``s to the right of ``self``.

        :param others: The BVs to concatenate onto the right side of ``self`` in order.

        Returns:
            BV: a bit vector with the bits from ``self`` on the left and the bits from
                ``others`` in order on the right.
        """
        return reduce(lambda acc, b: acc.__concat_single(b), others, self)

    @staticmethod
    def join(*bs : 'BV') -> 'BV':
        """Concatenate the given ``BV``s in order.

        :param bs: The ``BV``s to concatenate in order.

        Returns:
            BV: A bit vector with the bits from ``others`` in order.
        """
        return reduce(lambda acc, b: acc.__concat_single(b), bs, BV(0,0))

    def zero(self) -> 'BV':
        """The zero bit vector for ``self``'s size (i.e., ``BV(self.size(), 0)``)."""
        return BV(self.size() ,0)

    def to_int(self) -> int:
        """Return the unsigned integer the ``BV`` represents (equivalent to ``self.value()``)."""
        return self.__value

    def to_signed_int(self) -> int:
        """Return the signed (i.e., two's complement) integer the ``BV`` represents."""
        if self.__size == 0 or not self.msb():
            n = self.__value
        else:
            n = 0 - ((2 ** self.__size) - self.__value)
        return n

    def msb(self) -> bool:
        """Returns ``True`` if the most significant bit is 1, else returns ``False``."""
        if self.__size == 0:
            raise ValueError("0-length BVs have no most significant bit.")
        else:
            return self[self.__size - 1]

    def lsb(self) -> bool:
        """Returns ``True`` if the least significant bit is 1, else returns ``False``."""
        if self.__size == 0:
            raise ValueError("0-length BVs have no least significant bit.")
        else:
            return self[0]


    def __eq__(self, other : Any) -> bool:
        """Returns ``True`` if ``other`` is also a ``BV`` of the same size and value, else returns ``False``."""
        if isinstance(other, BV):
            return self.__size == other.__size and self.__value == other.__value
        else:
            return False

    def __index__(self) -> int:
        """Equivalent to ``self.value()``."""
        return self.__value

    def __int__(self) -> int:
        """Equivalent to ``self.value()``."""
        return self.__value

    def __len__(self) -> int:
        """Equivalent to ``self.size()``."""
        return self.__size

    def __bytes__(self) -> bytes:
        """Returns the ``bytes`` value equivalent to ``self.value()``."""
        byte_len = (self.__size // 8) + (0 if self.__size % 8 == 0 else 1)
        return self.__value.to_bytes(byte_len, 'big')


    def split(self, size : int) -> List['BV']:
        """Split ``self`` into a list of ``BV``s of length ``size``.

        :param size: Size of segments to partition ``self`` into (must evently divide ``self.size()``).
        """
        if not isinstance(size, int) or size <= 0:
            raise ValueError(f'`size` argument to splits must be a positive integer, got {size!r}')
        if not self.size() % size == 0:
            raise ValueError(f'{self!r} is not divisible into equal parts of size {size!r}')
        mask = (1 << size) - 1
        return [BV(size, (self.__value >> (i * size)) & mask)
                for i in range(self.size() // size - 1, -1, -1)]


    def popcount(self) -> int:
        """Return the number of bits set to ``1`` in ``self``."""
        return bin(self).count("1")

    @staticmethod
    def from_bytes(bs : Union[bytes,bytearray], *, size : Optional[int] = None, byteorder : ByteOrder = 'big') -> 'BV':
        """Convert the given bytes ``bs`` into a ``BV``.

        :param bs: Bytes to convert to a ``BV``.
        :param size, optional: Desired ``BV``'s size (must be large enough to represent ``bs``). The
            default (i.e., ``None``) will result in a ``BV`` of size ``len(bs) * 8``.
        :param byteorder, optional: Byte ordering ``bs`` should be interpreted as, defaults to
            ``'big'``, ``little`` being the other acceptable value. Equivalent to the ``byteorder``
            parameter from Python's ``int.from_bytes``."""

        if isinstance(bs, bytearray):
            bs = bytes(bs)
        elif not isinstance(bs, bytes):
            raise ValueError(f"from_bytes given not a bytearray or bytes value: {bs!r}")

        if not byteorder == 'little' and not byteorder == 'big':
            raise ValueError("byteorder must be either 'little' or 'big'")

        if size == None:
            return BV(len(bs) * 8, int.from_bytes(bs, byteorder=byteorder))
        elif isinstance(size, int) and size >= len(bs) * 8:
            return BV(size, int.from_bytes(bs, byteorder=byteorder))
        else:
            raise ValueError(f'from_bytes given invalid bit size {size!r} for bytes {bs!r}')

    def with_bit(self, index : int, set_bit : bool) -> 'BV':
        """Return a ``BV`` identical to ``self`` but with the bit at ``index`` set to
        ``1`` if ``set_bit == True``, else ``0``."""
        if index < 0 or index >= self.__size:
            raise ValueError(f'{index!r} is not a valid bit index for {self!r}')
        if set_bit:
            mask = (1 << index)
            return BV(self.__size, self.__value | mask)
        else:
            mask = (2 ** self.__size - 1) ^ (1 << index)
            return BV(self.__size, self.__value & mask)


    def with_bits(self, low : int, bits : 'BV') -> 'BV':
        """Return a ``BV`` identical to ``self`` but with the bits from ``low`` to
        ``low + bits.size() - 1`` replaced by the bits from ``bits``."""
        if not isinstance(low, int) or low < 0 or low >= self.__size:
            raise ValueError(f'{low!r} is not a valid low bit index for {self!r}')
        elif not isinstance(bits, BV):
            raise ValueError(f'Expected a BV but got {bits!r}')
        elif low + bits.size() > self.__size:
            raise ValueError(f'{bits!r} does not fit within {self!r} when starting from low bit index {low!r}.')
        else:
            wider = self.size() - (low + bits.size())
            mask = (BV(bits.size(), 2 ** bits.size() - 1) << low).widen(wider)
            return (self & ~mask) | (bits << low).widen(wider)

    def to_bytes(self) -> bytes:
        """Convert the given ``BV`` into a python native ``bytes`` value.
        
        Note: equivalent to bytes(_)."""

        return self.__bytes__()

    def __mod_if_overflow(self, value : int) -> int:
        n : int = value if value.bit_length() <= self.__size \
                   else (value % (2 ** self.__size))
        return n

    def __add__(self, other : Union[int, 'BV']) -> 'BV':
        """Addition bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                return BV(
                    self.__size,
                    self.__mod_if_overflow(self.__value + other.__value))
            else:
                raise ValueError(self.__unequal_len_op_error_msg("+", other))
        elif isinstance(other, int):
            return BV(
                self.__size,
                self.__mod_if_overflow(self.__value + other))
        else:
            raise ValueError(f'Cannot add {self!r} with {other!r}.')
    
    def __radd__(self, other : int) -> 'BV':
        if isinstance(other, int):
            return BV(self.__size, self.__mod_if_overflow(self.__value + other))
        else:
            raise ValueError(f'Cannot add {self!r} with {other!r}.')   

    def __and__(self, other : Union['BV', int]) -> 'BV':
        """Bitwise 'logical and' bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                return BV(self.__size, self.__value & other.__value)
            else:
                raise ValueError(self.__unequal_len_op_error_msg("&", other))
        elif isinstance(other, int):
            return BV(self.__size, self.__value & other)
        else:
            raise ValueError(f'Cannot bitwise and {self!r} with value {other!r}.')

    def __rand__(self, other : int) -> 'BV':
        if isinstance(other, int):
            return BV(self.__size, self.__value & other)
        else:
            raise ValueError(f'Cannot bitwise and {self!r} with value {other!r}.')
    
    def __or__(self, other : Union['BV', int]) -> 'BV':
        """Bitwise 'logical or' bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                return BV(self.__size, self.__value | other.__value)
            else:
                raise ValueError(self.__unequal_len_op_error_msg("|", other))
        elif isinstance(other, int):
            return BV(self.__size, self.__value | other)
        else:
            raise ValueError(f'Cannot bitwise or {self!r} with value {other!r}.')

    def __ror__(self, other : int) -> 'BV':
        if isinstance(other, int):
            return BV(self.__size, self.__value | other)
        else:
            raise ValueError(f'Cannot bitwise or {self!r} with value {other!r}.')

    def __xor__(self, other : Union['BV', int]) -> 'BV':
        """Bitwise 'logical xor' bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                return BV(self.__size, self.__value ^ other.__value)
            else:
                raise ValueError(self.__unequal_len_op_error_msg("^", other))
        elif isinstance(other, int):
            return BV(self.__size, self.__value ^ other)
        else:
            raise ValueError(f'Cannot bitwise xor {self!r} with value {other!r}.')

    def __rxor__(self, other : int) -> 'BV':
        if isinstance(other, int):
            return BV(self.__size, self.__value ^ other)
        else:
            raise ValueError(f'Cannot bitwise xor {self!r} with value {other!r}.')


    def __invert__(self) -> 'BV':
        """Returns the bitwise inversion of ``self``."""
        return BV(self.__size, (1 << self.__size) - 1 - self.__value)

    @staticmethod
    def __from_signed_int(size: int, val : int) -> 'BV':
        excl_max = 2 ** size
        if (size == 0):
            return BV(0,0)
        elif val >= 0:
            return BV(size, val % excl_max)
        else:
            return BV(size, ((excl_max - 1) & ~(abs(val + 1))) % excl_max)

    @staticmethod
    def from_signed_int(size: int, value : int) -> 'BV':
        """Returns the ``BV`` corrsponding to the ``self.size()``-bit two's complement representation of ``value``.

        :param size: Bit width of desired ``BV``.
        :param value: Integer returned ``BV`` is derived from (must be in range
            ``-(2 ** (size - 1))`` to ``(2 ** (size - 1) - 1)`` inclusively).
        """
        if size == 0:
            raise ValueError("There are no two's complement 0-bit vectors.")
        max_val = 2 ** (size - 1) - 1
        min_val = -(2 ** (size - 1))
        if value < min_val or value > max_val:
            raise ValueError(f'{value!r} is not in range [{min_val!r},{max_val!r}].')
        else:
            return BV.__from_signed_int(size, value)

    def __sub__(self, other : Union[int, 'BV']) -> 'BV':
        """Subtraction bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                if self.__size == 0:
                    return self
                else:
                    return BV.__from_signed_int(
                        self.__size,
                        self.to_signed_int() - other.to_signed_int())
            else:
                raise ValueError(self.__unequal_len_op_error_msg("-", other))
        elif isinstance(other, int):
            self.__check_int_size(other)
            if self.__size == 0:
                return self
            else:
                return BV.__from_signed_int(
                    self.__size,
                    self.to_signed_int() - other)
        else:
            raise ValueError(f'Cannot subtract {other!r} from {self!r}.')

    def __rsub__(self, other : int) -> 'BV':
        if isinstance(other, int):
            self.__check_int_size(other)
            if self.__size == 0:
                return self
            else:
                return BV.__from_signed_int(
                        self.__size,
                        other - self.to_signed_int())
        else:
            raise ValueError(f'Cannot subtract {self!r} from {other!r}.')


    def __mul__(self, other: Union[int, 'BV']) -> 'BV':
        """Multiplication bewteen ``BV``s of equal size or bewteen a ``BV`` and a nonnegative
           integer whose value is expressible with the ``BV`` parameter's size."""
        if isinstance(other, BV):
            if self.__size == other.__size:
                return BV(
                    self.__size,
                    self.__mod_if_overflow(self.__value * other.__value))
            else:
                raise ValueError(self.__unequal_len_op_error_msg("*", other))
        elif isinstance(other, int):
            self.__check_int_size(other)
            return BV.__from_signed_int(
                self.__size, 
                self.__mod_if_overflow(self.__value * other))
        else:
            raise ValueError(f'Cannot multiply {self!r} and {other!r}.')

    def __rmul__(self, other : int) -> 'BV':
        return self.__mul__(other)

    
    def __lshift__(self, other : Union[int, 'BV']) -> 'BV':
        """Returns the bitwise left shift of ``self``.

        :param other: Nonnegative amount to left shift ``self`` by (resulting
            ``BV``'s size is ``self.size() + int(other)``)).
        """
        if isinstance(other, int) or isinstance(other, BV):
            n = int(other)
            if n < 0:
                raise ValueError(f'Cannot left shift a negative amount (i.e, {n!r}).')
            return BV(self.__size + n, self.__value << n)
        else:
            raise ValueError(f'Shift must be specified with an integer or BV, but got {other!r}.')


    def __rshift__(self, other : Union[int, 'BV']) -> 'BV':
        """Returns the bitwise right shift of ``self``.

        :param other: Nonnegative amount to right shift ``self`` by (resulting
            ``BV``'s size is ``max(0, self.size() - int(other))``).
        """
        if isinstance(other, int) or isinstance(other, BV):
            n = int(other)
            if n < 0:
                raise ValueError(f'Cannot right shift a negative amount (i.e, {n!r}).')
            return BV(max(0, self.__size - n), self.__value >> n)
        else:
            raise ValueError(f'Shift must be specified with an integer or BV, but got {other!r}.')

    def __check_int_size(self, val : int) -> None:
        if val >= (2 ** self.__size) or val < 0:
            raise ValueError(f'{val!r} is not a valid unsigned {self.__size!r}-bit value.')


    def __unequal_len_op_error_msg(self, op : str, other : 'BV') -> str:
        return f'Operator `{op}` cannot be called on BV of unequal length {self!r} and {other!r}.'
