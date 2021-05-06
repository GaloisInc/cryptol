import unittest
from pathlib import Path
import unittest
from cryptol.scryptol import *
from cryptol.bitvector import BV
from cryptol.cryptolvalues import *


class TestCryValues(unittest.TestCase):
    def test_CryValues(self):
        connect(reset_server=True)
        load_file(str(Path('tests','scryptol','test-files','Types.cry')))

        exWord = CryBV(8, 42)
        self.assertEqual(to_cryptol_value(evalCry("exWord")), exWord)
        exInteger = CryInt(257)
        self.assertEqual(to_cryptol_value(evalCry("exInteger")), exInteger)
        exZ = CryIntMod(1,12)
        self.assertEqual(to_cryptol_value(evalCry("exZ")), exZ)
        exTuple = CryTuple(exWord, exInteger, exZ)
        self.assertEqual(to_cryptol_value(evalCry("exTuple")), exTuple)
        exSeq = CrySeq([1,3,5,7,9])
        self.assertEqual(to_cryptol_value(evalCry("exSeq")), exSeq)
        exRecord = CryRec(x=True, y=CryRec(a=exSeq))
        self.assertEqual(to_cryptol_value(evalCry("exRecord")), exRecord)

        # quoted cryptol

        a = cryQ('g x')
        b = cryQ(f'foo {a}')
        self.assertEqual(str(b), '(foo (g x))')

        b = CryBit(True)
        q = cryQ("1")
        self.assertEqual(str(b & q), '((True : Bit) && (1))')

        xs = CrySeq([1,3,5,7,9])
        x = (xs ** cryQ('i')) + CrySeq([0,1,0,1,0])
        self.assertEqual(str(x), '((([1, 3, 5, 7, 9] : [5]Integer) ^^ (i)) + ([0, 1, 0, 1, 0] : [5]Integer))')

        # sequences

        self.assertEqual(repr(CryBV(8,0x5A)), repr(CrySeq([False, True, False, True, True, False, True, False])))

        self.assertEqual(xs << CryBV(8,2), [5,7,9,0,0])

        xtups = CrySeq([CryTuple(0,CrySeq("ABC")),
                        CryTuple(1,CrySeq("DEF")),
                        CryTuple(2,CrySeq("GHI"))])
        self.assertEqual(xtups << 1, CrySeq([CryTuple(1,CrySeq("DEF")),
                                             CryTuple(2,CrySeq("GHI")),
                                             CryTuple(0,CrySeq([CryBV(8,0),CryBV(8,0),CryBV(8,0)]))]))

        self.assertEqual(CryBV(8,101).valueAsList(), [False,True,True,False,False,True,False,True])

        # tuples

        self.assertEqual(CryTuple(0,5,4) + CryTuple(1,1,1), CryTuple(1,6,5))

        # records

        self.assertEqual(CryRec(a=5,b=2), CryRec(b=2,a=5))
        self.assertEqual(CryRec(a=5,b=2) + CryRec(b=1,a=1), CryRec(a=6,b=3))
        self.assertTrue(CryRec(b=10,a=0) < CryRec(a=10,b=0))
        self.assertTrue(CryRec(b=0,a=10) > CryRec(b=10,a=0))
        self.assertEqual(CryRec(a=5,b=2).a, CryInt(5))


if __name__ == "__main__":
    unittest.main()
