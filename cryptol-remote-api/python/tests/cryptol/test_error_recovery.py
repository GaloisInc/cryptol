import unittest
from pathlib import Path
import unittest
import cryptol
from argo_client.interaction import ArgoException
from cryptol.cryptoltypes import CryptolApplication, CryptolLiteral
from cryptol.bitvector import BV


class TestErrorRecovery(unittest.TestCase):
    def test_ErrorRecovery(self):
        c = cryptol.connect()
        
        with self.assertRaises(ArgoException):
            c.load_file(str(Path('tests','cryptol','test-files','bad.cry'))).result()
        
        # test that loading a valid file still works after an exception
        c.load_file(str(Path('tests','cryptol','test-files','Foo.cry'))).result()

        # test that a reset still works after an exception
        c.reset()


if __name__ == "__main__":
    unittest.main()
