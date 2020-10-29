import os

from cryptol import CryptolConnection, CryptolContext, cry
import cryptol
import cryptol.cryptoltypes
from BitVector import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = cryptol.connect("cabal new-exec --verbose=0 cryptol-remote-api")

c.change_directory(dir_path)

c.load_file("Foo.cry")

x_val = c.evaluate_expression("x").result()

assert c.evaluate_expression("Id::id x").result() == x_val
assert c.call('Id::id', bytes.fromhex('ff')).result() == bytes.fromhex('ff')


assert c.call('add', b'\0', b'\1').result() == b'\x01'
assert c.call('add', bytes.fromhex('ff'), bytes.fromhex('03')).result() == bytes.fromhex('02')

cryptol.add_cryptol_module('Foo', c)
from Foo import *
assert add(b'\2', 2) == b'\4'

assert add(BitVector( intVal = 0, size = 8 ), BitVector( intVal = 1, size = 8 )) == bytes.fromhex('01')
assert add(BitVector( intVal = 1, size = 8 ), BitVector( intVal = 2, size = 8 )) == bytes.fromhex('03')
assert add(BitVector( intVal = 255, size = 8 ), BitVector( intVal = 1, size = 8 )) == bytes.fromhex('00')
