# -*- coding utf-8 -*-
"""
Module for controlling a Cryptol session from python.
"""

import pexpect

def interruptable(method):
    """
    Decorator for methods that can be sent a KeyboardInterrupt
    exception; passes a Ctrl-C to the underlying cryptol process
    """
    def inner(self, *args):
        result = None
        try:
            result = method(self, *args)
        except KeyboardInterrupt:
            self.cryptol.sendcontrol('c')
            raise Cryptol2Interrupt()
        return result
    return inner


class Cryptol2Py:

    def __init__(self):
        self.cryptol = setup_cryptol_process()
        self.cryptol.expect("<READY>")

    def stop(self):
        self.cryptol.sendcontrol('c')

    @interruptable
    def runInteractive(self, code):
        out = []
        for line in code.splitlines():
            self.cryptol.sendline(line)
            self.cryptol.expect("<DONE>", timeout=600)
            out.append(self.cryptol.before)
        return '\n'.join(out)

    @interruptable
    def addModuleFragment(self, code):
        self.cryptol.sendline("<BEGINMOD>")
        if code[-1] == '\n':
            self.cryptol.send(code)
        else:
            self.cryptol.sendline(code)
        self.cryptol.sendline("<ENDMOD>")
        self.cryptol.expect("<DONE>")
        return self.cryptol.before

    @interruptable
    def runAuto(self, code):
        """
        Send a block of code to the cryptol process using the AUTO input
        mode. This will attempt to automatically determine whether the
        input is a module fragment or a sequence of interactive
        commands.
        """
        self.cryptol.sendline("<BEGINAUTO>")
        if code[-1] == '\n':
            self.cryptol.send(code)
        else:
            self.cryptol.sendline(code)
        self.cryptol.sendline("<ENDAUTO>")
        self.cryptol.expect("<DONE>", timeout=600)
        return self.cryptol.before

def setup_cryptol_process():
    """
    Static method that setups up an interactive cryptol process.
    """
    cryptol = pexpect.spawn("../cabal-dev/bin/cryptol2nb")
    cryptol.setecho(False)
    return cryptol

class Cryptol2PyError:
    pass

class Cryptol2Interrupt:
    def _render_traceback_(self):
        return ["<interrupted>"]

def test():
    cry = Cryptol2Py()
    return cry.runAuto("1+1")

if __name__ == "__main__":
    print test()
