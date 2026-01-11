[![Cryptol](https://github.com/GaloisInc/cryptol/workflows/Cryptol/badge.svg)](https://github.com/GaloisInc/cryptol/actions?query=workflow%3ACryptol)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/GaloisInc/cryptol)


# Cryptol, version 3

    This version of Cryptol is (C) 2013-2024 Galois, Inc., and
    distributed under a standard, three-clause BSD license. Please see
    the file LICENSE, distributed with this software, for specific
    terms and conditions.

# What is Cryptol?

The Cryptol specification language was designed by Galois for the NSA
Laboratory for Advanced Cybersecurity Research as a public standard for
specifying cryptographic algorithms. A Cryptol reference specification
can serve as the formal documentation for a cryptographic module.
Unlike current specification mechanisms, Cryptol is fully executable,
allowing designers to experiment with their programs incrementally as
their designs evolve.

This release is an interpreter for version 3 of the Cryptol
language. The interpreter includes a `:check` command, which tests
predicates written in Cryptol against randomly-generated test vectors
(in the style of
[QuickCheck](http://hackage.haskell.org/package/QuickCheck)). There is
also a `:prove` command, which calls out to SMT solvers, such as
Yices, Z3, CVC4, or CVC5, to prove predicates for all possible inputs.

# Getting Cryptol Binaries

Cryptol binaries for Mac OS X, Linux, and Windows are available from the
GitHub [releases page](https://github.com/GaloisInc/cryptol/releases).
Mac OS X and Linux binaries are distributed as a tarball which you can
extract to a location of your choice. Windows binaries are distributed
both as tarballs and as `.msi` installer packages which place a shortcut
to the Cryptol interpreter in the Start menu.

On Mac OS X, Cryptol is also available via
[Homebrew](http://brew.sh/). Simply run `brew update && brew install cryptol`
to get the latest stable version.

## Getting Z3

Cryptol currently uses Microsoft Research's [Z3 SMT
solver](https://github.com/Z3Prover/z3) by default to solve constraints
during type checking, and as the default solver for the `:sat` and
`:prove` commands.  Cryptol generally requires the most recent version
of Z3, but you can see the specific version tested in CI by looking [here](https://github.com/GaloisInc/what4-solvers/releases/tag/snapshot-20251112).

You can download Z3 binaries for a variety of platforms from their
[releases page](https://github.com/Z3Prover/z3/releases). If you
install Cryptol using Homebrew, the appropriate version of Z3 will be
installed automatically. If you're using Linux, the package manager for
your distribution may include Z3, as well, though sometimes the
available versions are somewhat old.

After installation, make sure that `z3` (or `z3.exe` on Windows)
is on your PATH.

### Note for 64-bit Linux Users

On some 64-bit Linux configurations, 32-bit binaries do not work. This
can lead to unhelpful error messages like `z3: no such file or
directory`, even when `z3` is clearly present. To fix this, either
install 32-bit compatibility packages for your distribution, or download
the `x64` version of Z3.

# Building Cryptol From Source

In addition to the binaries, the Cryptol source is available publicly
on [GitHub](https://github.com/GaloisInc/cryptol).

Cryptol builds and runs on various flavors of Linux, Mac OS X, and
Windows. We regularly build and test it in the following environments:

- macOS 15 (ARM64 and x86-64)
- Ubuntu 22.04 (x86-64)
- Ubuntu 24.04 (x86-64)
- Windows Server 2022 (x86-64)

## Prerequisites

Cryptol is regularly built and tested with three recent
versions of GHC, which at the time of this writing are 9.4.8, 9.6.7, and
9.8.4. The easiest way to install an appropriate version of GHC is
with [ghcup](https://www.haskell.org/ghcup/).

Some supporting non-Haskell libraries are required to build
Cryptol. Most should already be present for your operating system, but
you may need to install the following:

- [The GNU Multiple Precision Arithmetic Library (GMP)](https://gmplib.org/)
- [ncurses](https://www.gnu.org/software/ncurses/)

You'll also need [Z3](#getting-z3) installed when running Cryptol.

## Building Cryptol

After a fresh checkout of cryptol, be sure to initialize its git submodules:

    git submodule update --init

Then, from the Cryptol source directory, run:

    ./cry build

This will build Cryptol in place. From there, there are additional targets:

- `./cry run`: run Cryptol in the current directory
- `./cry test`: run the regression test suite

## Installing Cryptol

If you run `cabal v2-install --installdir=DIR` in your source directory
after running one of the above `./cry` command, you will end up with a
binary in `DIR`.

## Configuring Cryptol

Cryptol can use several external files to control its operation.
Normally, the build process embeds these files into the executable.
However, these embedded files can be overwritten with local copies in
two ways:

- Copy the contents of the `lib` directory into `$HOME/.cryptol`.

- Set the `CRYPTOLPATH` environment variable to name some other
  directory that contains the files from the `lib` directory.

# Contributing

We believe that anyone who uses Cryptol is making an important
contribution toward making Cryptol a better tool. There are many ways
to get involved.

## Users

If you write Cryptol programs that you think would benefit the
community, fork the GitHub repository, and add them to the
`examples/contrib` directory and submit a pull request.

We host a Cryptol mailing list, which you can [join
here](https://groups.google.com/a/galois.com/forum/#!forum/cryptol-users).

If you run into a bug in Cryptol, if something doesn't make sense in the
documentation, if you think something could be better, or if you just
have a cool use of Cryptol that you'd like to share with us, use the
issues page on [GitHub](https://github.com/GaloisInc/cryptol), or send
email to <cryptol@galois.com>.

## Developers

If you'd like to get involved with Cryptol development, see the list of
[low-hanging
fruit](https://github.com/GaloisInc/cryptol/labels/low-hanging%20fruit).
These are tasks which should be straightforward to implement. Make a
fork of this GitHub repository, send along pull requests and we'll be
happy to incorporate your changes.

### Repository Structure

- `/cryptol`: Haskell sources for the front-end `cryptol` executable
  and read-eval-print loop
- `/docs`: LaTeX and Markdown sources for the Cryptol documentation
- `/examples`: Cryptol sources implementing several interesting
  algorithms
- `/lib`: Cryptol standard library sources
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

For a large collection of Cryptol examples, see the [cryptol-specs
repository](https://github.com/galoisinc/cryptol-specs).

Cryptol is still under active development at Galois. We are also
building tools that consume both Cryptol specifications and
implementations in (for example) C or Java, and can (with some amount of
work) allow you to verify that an implementation meets its
specification. See more information on the [SAW
website](https://saw.galois.com).

# Thanks!

We hope that Cryptol is useful as a tool for educators and students,
commercial and open source authors of cryptographic implementations,
and by cryptographers to

- specify cryptographic algorithms
- check or prove properties of algorithms
- generate test vectors for testing implementations
- experiment with new algorithms

## Acknowledgements

Cryptol has been under development for over a decade with many people
contributing to its design and implementation. Those people include (but are
not limited to) Aaron Tomb, Adam Foltzer, Adam Wick, Alexander Bakst, Andrew
Kent, Andrei Stefanescu, Andrey Chudnov, Andy Gill, Benjamin Barenblat, Ben
Jones, Ben Selfridge, Brett Boston, Bretton Chen, Brian Huffman, Brian Ledger,
Chris Phifer, Daniel Wagner, David Thrane Christiansen, David Lazar, Dylan
McNamee, Eddy Westbrook, Edward Yang, Eric Mertens, Eric Mullen, Fergus
Henderson, Hazel Weakly, Henry Blanchette, Iavor Diatchki, Jeff Lewis, Jim
Teisher, Joe Hendrix, Joe Hurd, Joe Kiniry, Joel Stanley, Joey Dodds, John
Launchbury, John Matthews, Jonathan Daugherty, Kenneth Foner, Kevin Quick, Kyle
Carter, Ledah Casburn, Lee Pike, Levent Erkök, Lisanna Dettwyler, Magnus
Carlsson, Mark Shields, Mark Tullsen, Matt Sottile, Matthew Yacavone, Nathan
Collins, Philip Weaver, Robert Dockins, Ryan Scott, Sally Browning, Sam
Anklesaria, Sigbjørn Finne, Stephen Magill, Thomas Nordin, Trevor Elliott, and
Tristan Ravitch.

Much of the work on Cryptol has been funded by, and lots of design input
was provided by, the team at the [NSA's Laboratory for Advanced Cybersecurity
Research](https://www.nsa.gov/Research/NSA-Mission-Oriented-Research/LAC/),
including Brad Martin, Frank Taylor, and Sean Weaver.

Portions of Cryptol are also based upon work supported by the Office
of Naval Research under Contract No. N68335-17-C-0452. Any opinions,
findings and conclusions or recommendations expressed in this
material are those of the author(s) and do not necessarily reflect
the views of the Office of Naval Research.
