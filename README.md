# Cryptol, version 2

    This version of Cryptol is (C) 2013-2014 Galois, Inc., and
    distributed under a standard, three-clause BSD license. Please see
    the file LICENSE, distributed with this software, for specific
    terms and conditions.

# What is Cryptol?

The Cryptol specification language was designed by Galois for the
NSA's Trusted Systems Research Group as a public standard for
specifying cryptographic algorithms. A Cryptol reference specification
can serve as the formal documentation for a cryptographic module.
Unlike current specification mechanisms, Cryptol is fully executable,
allowing designers to experiment with their programs incrementally as
their designs evolve.

This release is an interpreter for version 2 of the Cryptol
language. The interpreter includes a `:check` command, which tests
predicates written in Cryptol against randomly-generated test vectors
(in the style of
[QuickCheck](http://hackage.haskell.org/package/QuickCheck). There is
also a `:prove` command, which calls out to SMT solvers, such as
Yices, Z3, or CVC4, to prove predicates for all possible inputs.

# Getting Cryptol Binaries

Cryptol binaries for Mac OS X, Linux, and Windows are available from
the GitHub
[releases page](https://github.com/GaloisInc/cryptol/releases). Mac OS
X and Linux binaries are distributed as a tarball which you can
extract to a location of your choice. Windows binaries are distributed
as an `.msi` installer package which places a shortcut to the Cryptol
interpreter in the Start menu.

## Getting CVC4

Cryptol currently depends on the
[CVC4 SMT solver](http://cvc4.cs.nyu.edu/) to solve constraints during
type checking, and as the default solver for the `:sat` and `:prove`
commands. You can download CVC4 binaries for a variety of platforms
from their [download page](http://cvc4.cs.nyu.edu/downloads/).

# Building Cryptol From Source

In addition to the binaries, the Cryptol source is available publicly
on [GitHub](https://github.com/GaloisInc/cryptol).

Cryptol builds and runs on various flavors of Linux, Mac OS X, and
Windows. We regularly build and test it in the following environments:

- Mac OS X 10.9 64-bit
- CentOS 5 32/64-bit
- CentOS 6 32/64-bit
- Windows XP 32-bit

## Prerequisites

Cryptol is developed using GHC 7.6.3 and cabal-install 1.18. While you
can install these independently, the easiest way to get the correct
versions is to:

1.  Install [Haskell Platform 2013.2.0.0](http://www.haskell.org/platform/)

    **Mac Users**: the current version of the Haskell Platform has
    some incompatibilities with Mac OS X 10.9; it is easier to install
    GHC, cabal-install, alex, and happy from
    [MacPorts](https://www.macports.org/) or
    [Homebrew](http://brew.sh/).

1. Run `cabal update`

1. Run `cabal install cabal-install`

1. Add cabal-install's binary path to your `PATH` variable (usually `~/.cabal/bin`)

Some supporting non-Haskell libraries are required to build
Cryptol. Most should already be present for your operating system, but
you may need to install the following:

- [The GNU Multiple Precision Arithmetic Library (GMP)](https://gmplib.org/)
- [ncurses](https://www.gnu.org/software/ncurses/)

You'll also need [CVC4](#getting-cvc4) installed when running Cryptol.

## Building Cryptol

From the Cryptol source directory, run:

    make

This will build Cryptol in place. From there, there are additional targets:

- `make test`: run the regression test suite
- `make docs`: build the Cryptol documentation (requires
  [pandoc](http://johnmacfarlane.net/pandoc/) and
  [TeX Live](https://www.tug.org/texlive/))
- `make tarball`: build a tarball with a relocatable Cryptol binary and documentation
- `make dist`: build a platform-specific distribution. On all
  platforms except Windows, this is currently equivalent to `make
  tarball`. On Windows, this will build an `.msi` package using
  [WiX Toolset 3.7](http://wixtoolset.org/), which must be installed
  separately.

## Installing Cryptol

Aside from the `docs` target, these will leave you with a Cryptol
binary at `.cabal-sandbox/bin/cryptol` in your source directory. You
can either use that binary directly, or use the results of `tarball`
or `dist` to install Cryptol in a location of your choice.

# Checking your Installation

Run Cryptol, and at the prompt type:

    Cryptol> :prove True

If Cryptol responds

    Q.E.D.

then Cryptol is installed correctly. If it prints something like

    *** An error occurred.
    ***  Unable to locate executable for cvc4
    ***  Executable specified: "cvc4"

then make sure you've installed [CVC4](#getting-cvc4), and that the
binary is on your `PATH`.

# Contributing

We believe that anyone who uses Cryptol is making an important
contribution toward making Cryptol a better tool. There are many ways
to get involved.

## Users

If you write Cryptol programs that you think would benefit the
community, fork the GitHub repository, and add them to the
`examples/contrib` directory and submit a pull request.

We host a Cryptol mailing list, which
you can [join here](http://community.galois.com/mailman/listinfo/cryptol-users).

If you run into a bug in Cryptol, if something doesn't make sense in
the documentation, if you think something could be better, or if you
just have a cool use of Cryptol that you'd like to share with us, use
the issues page on [GitHub](https://github.com/GaloisInc/cryptol), or
send email to <cryptol@galois.com>.

## Developers

If you plan to do development work on the Cryptol interpreter, please
make a fork of the GitHub repository and send along pull
requests. This makes it easier for us to track development and to
incorporate your changes.

### Repository Structure

- `/cryptol`: Haskell sources for the front-end `cryptol` executable
  and read-eval-print loop
- `/docs`: LaTeX and Markdown sources for the Cryptol documentation
- `/examples`: Cryptol sources implementing several interesting
  algorithms
- `/lib`: Cryptol standard library sources
- `/notebook`: Experimental Cryptol IPython Notebook implementation
- `/sbv`: Haskell sources for the `sbv` library, derived from Levent
  Erkok's [`sbv` library](http://leventerkok.github.io/sbv/) (see
  `/sbv/LICENSE`)
- `/src`: Haskell sources for the `cryptol` library (the bulk of the
  implementation)
- `/tests`: Haskell sources for the Cryptol regression test suite, as
  well as the Cryptol sources and expected outputs that comprise that
  suite


# Where to Look Next

The `docs` directory of the installation package contains an
introductory book, the `examples` directory contains a number of
algorithms specified in Cryptol.

If you are familiar with version 1 of Cryptol, you should read the
`Version2Changes` document in the `docs` directory.

Cryptol is still under active development at Galois. We are also
building tools that consume both Cryptol specifications and
implementations in (for example) C or Java, and can (with some amount
of work) allow you to verify that an implementation meets its
specification. Email us at <cryptol@galois.com> if you're interested
in these capabilities.

# Thanks!

We hope that Cryptol is useful as a tool for educators and students,
commercial and open source authors of cryptographic implementations,
and by cryptographers to

 * specify cryptographic algorithms
 * check or prove properties of algorithms
 * generate test vectors for testing implementations
 * experiment with new algorithms

## Acknowledgements

Cryptol has been under development for over a decade with many people
contributing to its design and implementation. Those people include
(but are not limited to) Iavor Diatchki, Aaron Tomb, Adam Wick, Brian
Huffman, Dylan McNamee, Joe Kiniry, John Launchbury, Matt Sottile,
Adam Foltzer, Joe Hendrix, Trevor Elliott, Lee Pike, Mark Tullsen,
Levent Erkök, David Lazar, Joel Stanley, Jeff Lewis, Andy Gill, Edward
Yang, Ledah Casburn, Jim Teisher, Sigbjørn Finne, Mark Shields, Philip
Weaver, Magnus Carlsson, Fergus Henderson, Joe Hurd, Thomas Nordin,
John Matthews and Sally Browning. In addition, much of the work on
Cryptol has been funded by, and lots of design input was provided by
the team at the
[NSA's Trusted Systems Research Group](http://www.nsa.gov/research/ia_research/),
including Brad Martin, Frank Taylor and Sean Weaver.


