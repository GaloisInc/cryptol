import unittest
from pathlib import Path
import unittest
import cryptol
from argo_client.interaction import ArgoException
from cryptol.cryptoltypes import CryptolApplication, CryptolLiteral
from cryptol.bitvector import BV


class TestErrorRecovery(unittest.TestCase):
    def test_ErrorRecovery(self):
        c = cryptol.connect_sync()
        
        with self.assertRaises(ArgoException):
            c.load_file(str(Path('tests','cryptol','test-files','bad.cry')))
        
        # test that loading a valid file still works after an exception
        c.load_file(str(Path('tests','cryptol','test-files','Foo.cry')))
    
        # ensure that we really did load the file with no errors
        x_val1 = c.eval("x")
        x_val2 = c.eval("Id::id x")
        self.assertEqual(x_val1, x_val2)

        # test that a reset still works after an exception (this used to throw
        #  an error before the server even had a chance to respond because of
        #  the `connection.protocol_state()` call in `CryptolReset`)
        c.reset()


if __name__ == "__main__":
    unittest.main()
