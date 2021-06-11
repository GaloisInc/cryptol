from typing import Any

class OpaqueValue():
  """A value from the Cryptol server which cannot be directly represented and/or
  marshalled to an RPC client.

  Note that as far as Python is concerned these values are only equal to
  themselves. If a richer notion of equality is required then the server should
  be consulted to compute the result."""
  identifier : str

  def __init__(self, identifier : str) -> None:
    self.identifier = identifier

  def __str__(self) -> str:
    return self.identifier

  def __repr__(self) -> str:
      return f"Opaque({self.identifier!r})"

  def __eq__(self, other : Any) -> bool:
    if not isinstance(other, OpaqueValue):
        return False
    else:
      return self.identifier == other.identifier

  def __hash__(self) -> int:
      return hash(self.identifier)
