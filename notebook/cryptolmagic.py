# -*- coding: utf-8 -*-
"""
===========
cryptolmagic
===========

Magics for interacting with Cryptol2
"""

from pprint import pprint

from IPython.core.magic import Magics, magics_class, cell_magic
from IPython.core.displaypub import publish_display_data

from cryptol2py import Cryptol2Py

@magics_class
class Cryptol2Magics(Magics):
    """A set of magics useful for interactive work with Cryptol2
    """
    def __init__(self, shell):
        """
        Parameters
        ----------
        shell : IPython shell

        """
        super(Cryptol2Magics, self).__init__(shell)
        self.cryptol = Cryptol2Py()

    @cell_magic
    def icry(self, line, cell=None):
        '''
        Execute code in Cryptol2 and return results including errors if there are
        any.
        '''
        if None == cell:
            out = ""
        else:
            out = self.cryptol.runInteractive(cell)

        publish_display_data("cryptol2magic", {'text/plain' : out})

    @cell_magic
    def cry(self, line, cell=None):
        '''
        Add the code to the current module in the Cryptol2 context.
        '''
        if None == cell:
            out = ""
        else:
            out = self.cryptol.addModuleFragment(cell)

        publish_display_data("cryptol2magic", {'text/plain' : out})

    @cell_magic
    def cryauto(self, line, cell=None):
        """
        Execute code in either module or interactive mode in Cryptol 2,
        depending on which one successfully parses.
        """
        if None == cell:
            out = ""
        else:
            out = self.cryptol.runAuto(cell)

        publish_display_data("cryptol2magic", {'text/plain' : out})


def load_ipython_extension(ip):
    """
    We want the default magic to be cryauto, but we want to allow
    other magics to work if they are specified.
    """
    ip.register_magics(Cryptol2Magics)

    def new_run_cell(self, cell, **kwds):
        if cell.startswith("%"):
            newcell = cell
        else:
            newcell = "%%cryauto\n" + cell
        self.old_run_cell(newcell, **kwds)

    from IPython.core.interactiveshell import InteractiveShell
    func_type = type(InteractiveShell.run_cell)
    ip.old_run_cell = ip.run_cell
    ip.run_cell = func_type(new_run_cell, ip, InteractiveShell)
    ip.write("cryptolmagic loaded")
