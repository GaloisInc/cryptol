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
from .cryptoltypes import fail_with
from .quoting import cry, cry_f
from .commands import *
from .connection import *
# import everything from `.synchronous` except `connect` and `connect_stdio`
#  (since functions with those names were already imported from `.connection`)
from .synchronous import Qed, Safe, Counterexample, Satisfiable, Unsatisfiable, CryptolSyncConnection
# and add an alias `sync` for the `synchronous` module
from . import synchronous
sync = synchronous

__all__ = ['bitvector', 'commands', 'connection', 'cryptoltypes', 'opaque', 'quoting', 'single_connection', 'solver', 'synchronous']
