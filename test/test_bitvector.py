import unittest
import random
from cryptol.bitvector import BV
from BitVector import BitVector


class BVBaseTest(unittest.TestCase):
    """Base class for BV test cases."""

    def assertBVEqual(self, b, size, value):
        """Assert BV `b` has the specified `size` and `value`."""
        self.assertEqual(b.size(),  size)
        self.assertEqual(b.value(), value)

    
    def assertUnOpExpected(self, op_fn, expected_fn):
        """Assert `prop` holds for any BV value."""
        for width in range(0, 129):
            max_val = 2 ** width - 1
            for i in range(0, 100):
                b = BV(width, random.randint(0, max_val))
                # Put `b` in the assertion so we can see its value
                # on failed test cases.
                self.assertEqual((b, op_fn(b)), (b, expected_fn(b)))

    def assertBinOpExpected(self, op_fn, expected_fn):
        """Assert `prop` holds for any BV value."""
        for width in range(0, 129):
            max_val = 2 ** width - 1
            for i in range(0, 100):
                b1 = BV(width, random.randint(0, max_val))
                b2 = BV(width, random.randint(0, max_val))
                # Put `b1` and `b2` in the assertion so we can
                # see its value on failed test cases.
                self.assertEqual((b1,b2,op_fn(b1, b2)), (b1,b2,expected_fn(b1, b2)))


class BVBasicTests(BVBaseTest):
    def test_constructor1(self):
        b = BV(BitVector(intVal = 0, size = 8))
        self.assertBVEqual(b, 8, 0)
        b = BV(BitVector(intVal = 42, size = 8))
        self.assertBVEqual(b, 8, 42)
        
    def test_constructor2(self):
        b = BV(0,0)
        self.assertBVEqual(b, 0, 0)
        b = BV(value=16,size=8)
        self.assertBVEqual(b, 8, 16)
        b = BV(8,42)
        self.assertBVEqual(b, 8, 42)

    def test_constructor_fails(self):
        with self.assertRaises(ValueError):
            BV(8, 256)
        with self.assertRaises(ValueError):
            BV(8, -1)

    def test_hex(self):
        self.assertEqual(hex(BV(0,0)), "0x0")
        self.assertEqual(BV(0,0).hex(), "0x0")
        self.assertEqual(hex(BV(4,0)), "0x0")
        self.assertEqual(BV(4,0).hex(), "0x0")
        self.assertEqual(hex(BV(5,0)), "0x0")
        self.assertEqual(BV(5,0).hex(), "0x00")
        self.assertEqual(hex(BV(5,11)), "0xb")
        self.assertEqual(BV(5,11).hex(), "0x0b")
        self.assertEqual(hex(BV(8,255)), "0xff")
        self.assertEqual(BV(8,255).hex(), "0xff")
        self.assertEqual(hex(BV(9,255)), "0xff")
        self.assertEqual(BV(9,255).hex(), "0x0ff")

    def test_repr(self):
        self.assertEqual(repr(BV(0,0)), "BV(0, 0x0)")
        self.assertEqual(repr(BV(9,255)), "BV(9, 0x0ff)")

    def test_int(self):
        self.assertEqual(int(BV(0,0)), 0)
        self.assertEqual(int(BV(9,255)), 255)
        self.assertUnOpExpected(
            lambda b: BV(b.size(), int(b)),
            lambda b: b)

    def test_size(self):
        self.assertEqual(BV(0,0).size(), 0)
        self.assertEqual(BV(9,255).size(), 9)

    def test_len(self):
        self.assertEqual(len(BV(0,0)), 0)
        self.assertEqual(len(BV(9,255)), 9)

    def test_popcount(self):
        self.assertEqual(BV(0,0).popcount(), 0)
        self.assertEqual(BV(8,0).popcount(), 0)
        self.assertEqual(BV(8,1).popcount(), 1)
        self.assertEqual(BV(8,2).popcount(), 1)
        self.assertEqual(BV(8,3).popcount(), 2)
        self.assertEqual(BV(8,255).popcount(), 8)

    def test_eq(self):
        self.assertEqual(BV(0,0), BV(0,0))
        self.assertEqual(BV(8,255), BV(8,255))
        self.assertTrue(BV(8,255) == BV(8,255))
        self.assertFalse(BV(8,255) == BV(8,254))
        self.assertFalse(BV(8,255) == BV(9,255))

    def test_neq(self):
        self.assertNotEqual(BV(0,0), BV(1,0))
        self.assertNotEqual(BV(0,0), 0)
        self.assertNotEqual(0, BV(0,0))
        self.assertTrue(BV(0,0) != BV(1,0))
        self.assertTrue(BV(1,0) != BV(0,0))
        self.assertFalse(BV(0,0) != BV(0,0))
        self.assertTrue(BV(0,0) != 0)
        self.assertTrue(0 != BV(0,0))

    def test_widen(self):
        self.assertEqual(BV(0,0).widen(8), BV(8,0))
        self.assertEqual(BV(9,255).widen(8), BV(17,255))


    def test_add(self):
        self.assertEqual(BV(16,7) + BV(16,9), BV(16,16))
        self.assertEqual(BV(16,9) + BV(16,7), BV(16,16))
        self.assertEqual(BV(16,9) + BV(16,7) + 1, BV(16,17))
        self.assertEqual(1 + BV(16,9) + BV(16,7), BV(16,17))
        self.assertBinOpExpected(
            lambda b1, b2: b1 + b2,
            lambda b1, b2: BV(0,0) if b1.size() == 0 else
                           BV(b1.size(), (int(b1) + int(b2)) % ((2 ** b1.size() - 1) + 1)))
        with self.assertRaises(ValueError):
            BV(15,7) + BV(16,9)
                
    
    def test_bitewise_and(self):
        self.assertEqual(BV(0,0) & BV(0,0), BV(0,0))
        self.assertEqual(BV(8,0xff) & BV(8,0xff), BV(8,0xff))
        self.assertEqual(BV(8,0xff) & BV(8,42), BV(8,42))
        self.assertEqual(BV(16,7) & BV(16,9), BV(16,1))
        self.assertEqual(BV(16,9) & BV(16,7), BV(16,1))
        self.assertEqual(BV(16,9) & BV(16,7) & 1, BV(16,1))
        self.assertEqual(1 & BV(16,9) & BV(16,7), BV(16,1))
        self.assertUnOpExpected(
            lambda b: b & 0,
            lambda b: BV(b.size(), 0))
        self.assertUnOpExpected(
            lambda b: b & (2 ** b.size() - 1),
            lambda b: b)
        self.assertBinOpExpected(
            lambda b1, b2: b1 & b2,
            lambda b1, b2: BV(b1.size(), int(b1) & int(b2)))
        with self.assertRaises(ValueError):
            BV(15,7) & BV(16,9)

    def test_bitewise_not(self):
        self.assertEqual(~BV(0,0), BV(0,0))
        self.assertEqual(~BV(1,0b0), BV(1,0b1))
        self.assertEqual(~BV(8,0x0f), BV(8,0xf0))
        self.assertEqual(~BV(10,0b0001110101), BV(10,0b1110001010))
        self.assertEqual(~~BV(10,0b0001110101), BV(10,0b0001110101))
        self.assertUnOpExpected(
            lambda b: ~~b,
            lambda b: b)
        self.assertUnOpExpected(
            lambda b: ~b & b,
            lambda b: BV(b.size(), 0))


    def test_positional_index(self):
        self.assertFalse(BV(16,0b10)[0])
        self.assertTrue(BV(16,0b10)[1])
        self.assertFalse(BV(16,0b10)[3])
        self.assertFalse(BV(8,0b10)[7])
        with self.assertRaises(ValueError):
            BV(8,7)["Bad Index"]
        with self.assertRaises(ValueError):
            BV(8,7)[-1]
        with self.assertRaises(ValueError):
            BV(8,7)[8]

    def test_positional_slice(self):
        self.assertEqual(BV(0,0)[0:0], BV(0,0))
        self.assertEqual(BV(16,0b10)[2:0], BV(2,0b10))
        self.assertEqual(BV(16,0b10)[16:0], BV(16,0b10))
        self.assertEqual(BV(16,0b1100110011001100)[16:8], BV(8,0b11001100))
        with self.assertRaises(ValueError):
            BV(0,0)[2:0]
        with self.assertRaises(ValueError):
            BV(8,42)[0:1]
        with self.assertRaises(ValueError):
            BV(8,42)[9:0]
        with self.assertRaises(ValueError):
            BV(8,42)[8:-1]
        with self.assertRaises(ValueError):
            BV(8,42)[10:10]

    def test_concat(self):
        self.assertEqual(BV(0,0).concat(BV(0,0)), BV(0,0))
        self.assertEqual(BV(1,0b1).concat(BV(0,0b0)), BV(1,0b1))
        self.assertEqual(BV(0,0b0).concat(BV(1,0b1)), BV(1,0b1))
        self.assertEqual(BV(1,0b1).concat(BV(1,0b0)), BV(2,0b10))
        self.assertEqual(BV(1,0b0).concat(BV(1,0b1)), BV(2,0b01))
        self.assertEqual(BV(1,0b1).concat(BV(1,0b1)), BV(2,0b11))
        self.assertEqual(BV(5,0b11111).concat(BV(3,0b000)), BV(8,0b11111000))
        self.assertEqual(BV(0,0).concat(), BV(0,0))
        self.assertEqual(BV(0,0).concat(BV(2,0b10),BV(2,0b01)), BV(4,0b1001))
        self.assertBinOpExpected(
            lambda b1, b2: b1.concat(b2)[b2.size():0],
            lambda b1, b2: b2)
        self.assertBinOpExpected(
            lambda b1, b2: b1.concat(b2)[b1.size() + b2.size():b2.size()],
            lambda b1, b2: b1)
        with self.assertRaises(ValueError):
            BV(8,42).concat(42)
        with self.assertRaises(ValueError):
            BV(8,42).concat("Oops not a BV")

    def test_join(self):
        self.assertEqual(BV.join(), BV(0,0))
        self.assertEqual(BV.join(*[]), BV(0,0))
        self.assertEqual(BV.join(BV(8,42)), BV(8,42))
        self.assertEqual(BV.join(*[BV(8,42)]), BV(8,42))
        self.assertEqual(BV.join(BV(0,0), BV(2,0b10),BV(3,0b110)), BV(5,0b10110))
        self.assertEqual(BV.join(*[BV(0,0), BV(2,0b10),BV(3,0b110)]), BV(5,0b10110))

    def test_bytes(self):
        self.assertEqual(bytes(BV(0,0)), b'')
        self.assertEqual(bytes(BV(1,1)), b'\x01')
        self.assertEqual(bytes(BV(8,255)), b'\xff')
        self.assertEqual(bytes(BV(16,255)), b'\x00\xff')


    def test_zero(self):
        self.assertEqual(BV(0,0).zero(), BV(0,0))
        self.assertEqual(BV(9,255).zero(), BV(9,0))

    def test_msb(self):
        self.assertEqual(BV(8,0).msb(), False)
        self.assertEqual(BV(8,1).msb(), False)
        self.assertEqual(BV(8,127).msb(), False)
        self.assertEqual(BV(8,128).msb(), True)
        self.assertEqual(BV(8,255).msb(), True)
        with self.assertRaises(ValueError):
            BV(0,0).msb()


    def test_lsb(self):
        self.assertEqual(BV(8,0).lsb(), False)
        self.assertEqual(BV(8,1).lsb(), True)
        self.assertEqual(BV(8,127).lsb(), True)
        self.assertEqual(BV(8,128).lsb(), False)
        self.assertEqual(BV(8,255).lsb(), True)
        with self.assertRaises(ValueError):
            BV(0,0).lsb()

    def test_from_signed_int(self):
        self.assertEqual(BV.from_signed_int(8,127), BV(8,127))
        self.assertEqual(BV.from_signed_int(8,-128), BV(8,0x80))
        self.assertEqual(BV.from_signed_int(8,-1), BV(8,255))
        self.assertUnOpExpected(
            lambda b: b if b.size() == 0 else BV.from_signed_int(b.size(), b.to_signed_int()),
            lambda b: b)
        with self.assertRaises(ValueError):
            BV.from_signed_int(8,128)
        with self.assertRaises(ValueError):
            BV.from_signed_int(8,-129)

    def test_sub(self):
        self.assertEqual(BV(0,0) - BV(0,0), BV(0,0))
        self.assertEqual(BV(0,0) - 0, BV(0,0))
        self.assertEqual(0 - BV(0,0), BV(0,0))
        self.assertEqual(BV(8,5) - 3, BV(8,2))
        self.assertEqual(5 - BV(8,3), BV(8,2))
        self.assertEqual(BV(8,3) - BV(8,3), BV(8,0))
        self.assertEqual(BV(8,3) - BV(8,4), BV(8,255))
        self.assertEqual(BV(8,3) - BV(8,255), BV(8,4))
        self.assertEqual(BV(8,255) - BV(8,3), BV(8,252))
        self.assertEqual(BV(8,3) - 255, BV(8,4))
        self.assertEqual(255 - BV(8,3), BV(8,252))
        self.assertUnOpExpected(
            lambda b: b - b,
            lambda b: b.zero())
        self.assertUnOpExpected(
            lambda b: b - BV(b.size(), 2 ** b.size() - 1),
            lambda b: b + 1)
        with self.assertRaises(ValueError):
            BV(9,3) - BV(8,3)
        with self.assertRaises(ValueError):
            256 - BV(8,3)
        with self.assertRaises(ValueError):
            BV(8,3) - 256
        with self.assertRaises(ValueError):
            (-1) - BV(8,3)
        with self.assertRaises(ValueError):
            BV(8,3) - (-1)


    def test_mul(self):
        self.assertEqual(BV(8,5) * BV(8,4), BV(8,20))
        self.assertEqual(5 * BV(8,4), BV(8,20))
        self.assertEqual(4 * BV(8,5), BV(8,20))
        self.assertEqual(100 * BV(8,5), BV(8,0xf4))
        self.assertEqual(BV(8,5) * 100, BV(8,0xf4))
        self.assertUnOpExpected(
            lambda b: b * 3 if b.size() >= 3 else b.zero(),
            lambda b: b + b + b if b.size() >= 3 else b.zero())
        with self.assertRaises(ValueError):
            BV(9,3) * BV(8,3)
        with self.assertRaises(ValueError):
            256 * BV(8,3)
        with self.assertRaises(ValueError):
            BV(8,3) * 256
        with self.assertRaises(ValueError):
            (-1) * BV(8,3)
        with self.assertRaises(ValueError):
            BV(8,3) * (-1)

    def test_split(self):
        self.assertEqual(
            BV(8,0xff).split(1),
            [BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1),
             BV(1,0x1)])
        self.assertEqual(
            BV(9,0b100111000).split(3),
            [BV(3,0b100),
             BV(3,0b111),
             BV(3,0x000)])
        self.assertEqual(
            BV(64,0x0123456789abcdef).split(4),
            [BV(4,0x0),
             BV(4,0x1),
             BV(4,0x2),
             BV(4,0x3),
             BV(4,0x4),
             BV(4,0x5),
             BV(4,0x6),
             BV(4,0x7),
             BV(4,0x8),
             BV(4,0x9),
             BV(4,0xa),
             BV(4,0xb),
             BV(4,0xc),
             BV(4,0xd),
             BV(4,0xe),
             BV(4,0xf)])
        with self.assertRaises(ValueError):
            BV(9,3).split("4")
        with self.assertRaises(ValueError):
            BV(9,3).split(4)


    def test_from_bytes(self):
        self.assertEqual(BV.from_bytes(b''), BV(0,0))
        self.assertEqual(BV.from_bytes(b'', size=64), BV(64,0))
        self.assertEqual(BV.from_bytes(b'\x00'), BV(8,0))
        self.assertEqual(BV.from_bytes(b'\x01'), BV(8,1))
        self.assertEqual(BV.from_bytes(b'\x01', size=16), BV(16,1))
        self.assertEqual(BV.from_bytes(b'\x00\x01'), BV(16,1))
        self.assertEqual(BV.from_bytes(b'\x01\x00', byteorder='little'), BV(16,1))
        self.assertEqual(BV.from_bytes(b'\x01\x00'), BV(16,0x0100))
        self.assertEqual(BV.from_bytes(b'\x01\x00', byteorder='little'), BV(16,0x0001))
        self.assertEqual(BV.from_bytes(b'\x01\x00', size=32,byteorder='little'), BV(32,0x0001))

    def test_to_bytes(self):
        self.assertEqual(BV(0,0).to_bytes() ,b'')
        self.assertEqual(BV(8,0).to_bytes() ,b'\x00')
        self.assertEqual(BV(8,1).to_bytes() ,b'\x01')
        self.assertEqual(BV(16,1).to_bytes(), b'\x00\x01')


    def test_bitewise_or(self):
        self.assertEqual(BV(0,0) | BV(0,0), BV(0,0))
        self.assertEqual(BV(8,0xff) | BV(8,0x00), BV(8,0xff))
        self.assertEqual(BV(8,0x00) | BV(8,0xff), BV(8,0xff))
        self.assertEqual(BV(8,0x00) | 0xff, BV(8,0xff))
        self.assertEqual(0xff | BV(8,0x00), BV(8,0xff))
        self.assertEqual(BV(8,0x00) | BV(8,42), BV(8,42))
        self.assertUnOpExpected(
            lambda b: b | 0,
            lambda b: b)
        with self.assertRaises(ValueError):
            BV(15,7) | BV(16,9)
        with self.assertRaises(ValueError):
            BV(8,255) | 256
        with self.assertRaises(ValueError):
            256 | BV(8,9)
        with self.assertRaises(ValueError):
            BV(8,255) | -1
        with self.assertRaises(ValueError):
            -1 | BV(8,9)


    def test_bitewise_xor(self):
        self.assertEqual(BV(0,0) ^ BV(0,0), BV(0,0))
        self.assertEqual(BV(8,0xff) ^ BV(8,0x00), BV(8,0xff))
        self.assertEqual(BV(8,0x00) ^ BV(8,0xff), BV(8,0xff))
        self.assertEqual(BV(8,0x0f) ^ BV(8,0xff), BV(8,0xf0))
        self.assertEqual(BV(8,0xf0) ^ BV(8,0xff), BV(8,0x0f))
        self.assertUnOpExpected(
            lambda b: b ^ 0,
            lambda b: b)
        self.assertUnOpExpected(
            lambda b: b ^ ~b,
            lambda b: BV(b.size(), 2 ** b.size() - 1))
        with self.assertRaises(ValueError):
            BV(15,7) ^ BV(16,9)
        with self.assertRaises(ValueError):
            BV(8,255) ^ 256
        with self.assertRaises(ValueError):
            256 ^ BV(8,9)
        with self.assertRaises(ValueError):
            BV(8,255) ^ -1
        with self.assertRaises(ValueError):
            -1 ^ BV(8,9)

    def test_with_bit(self):
        self.assertEqual(BV(1,0).with_bit(0,True), BV(1,1))
        self.assertEqual(BV(1,1).with_bit(0,False), BV(1,0))
        self.assertEqual(BV(8,0b11001100).with_bit(0,True), BV(8,0b11001101))
        self.assertEqual(BV(8,0b11001100).with_bit(3,False), BV(8,0b11000100))
        self.assertEqual(BV(8,0b11001100).with_bit(7,False), BV(8,0b01001100))
        with self.assertRaises(ValueError):
            BV(8,0b11001100).with_bit(8,False)
        with self.assertRaises(ValueError):
            BV(8,0b11001100).with_bit(-1,False)

    def test_with_bits(self):
        self.assertEqual(BV(1,0b0).with_bits(0,BV(1,0b0)), BV(1,0b0))
        self.assertEqual(BV(1,0b0).with_bits(0,BV(1,0b1)), BV(1,0b1))
        self.assertEqual(BV(1,0b1).with_bits(0,BV(1,0b0)), BV(1,0b0))
        self.assertEqual(BV(8,0b11010101).with_bits(3,BV(3,0b101)), BV(8,0b11101101))
        self.assertEqual(BV(8,0b11010101).with_bits(5,BV(3,0b101)), BV(8,0b10110101))
        with self.assertRaises(ValueError):
            BV(8,0b11000101).with_bits(-1,BV(3,0b111))
        with self.assertRaises(ValueError):
            BV(8,0b11000101).with_bits(0,"bad")
        with self.assertRaises(ValueError):
            BV(8,0b11000101).with_bits(0,BV(9,0))
        with self.assertRaises(ValueError):
            BV(8,0b11000101).with_bits(1,BV(8,0))
