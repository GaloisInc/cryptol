"""Cryptol bindings from Python. Use :py:func:`cryptol.connect` to start a new connection."""

from __future__ import annotations

from typing import NoReturn

from . import cryptoltypes
from . import solver
from .bitvector import BV
from .commands import *
from .connection import *


__all__ = ['cryptoltypes', 'solver']


def fail_with(x : Exception) -> NoReturn:
    "Raise an exception. This is valid in expression positions."
    raise x


def cry(string : str) -> cryptoltypes.CryptolCode:
    return cryptoltypes.CryptolLiteral(string)
