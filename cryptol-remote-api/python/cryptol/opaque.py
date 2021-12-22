from typing import Any
from dataclasses import dataclass

# we freeze this class because ``OpaqueValue``s represent immutable objects
@dataclass(frozen=True)
class OpaqueValue():
  """A value from the Cryptol server which cannot be directly represented and/or
  marshalled to an RPC client.

  Note that as far as Python is concerned these values are only equal to
  themselves. If a richer notion of equality is required then the server should
  be consulted to compute the result."""
  identifier : str

  def __str__(self) -> str:
    return self.identifier
