"""Cryptol bindings from Python. Use :py:func:`cryptol.connect` to start a new connection."""

from __future__ import annotations

import base64
import os
from enum import Enum
from dataclasses import dataclass
from distutils.spawn import find_executable
from typing import Any, List, NoReturn, Optional, Union
from typing_extensions import Literal

import argo_client.interaction as argo
from argo_client.interaction import HasProtocolState
from argo_client.connection import DynamicSocketProcess, ServerConnection, ServerProcess, StdIOProcess, HttpProcess
from . import cryptoltypes
from . import solver
from .bitvector import BV
from .commands import *
from .connection import *


__all__ = ['bitvector', 'commands', 'connections', 'cryptoltypes', 'solver']


def fail_with(x : Exception) -> NoReturn:
    "Raise an exception. This is valid in expression positions."
    raise x


def cry(string : str) -> cryptoltypes.CryptolCode:
    return cryptoltypes.CryptolLiteral(string)
