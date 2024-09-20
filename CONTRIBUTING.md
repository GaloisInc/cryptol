# Cryptol development

This document explains our standards for developing Cryptol. Our goals
are to have a development process that:

- Consistently yields reliable software artifacts
- Quickly incorporates improvements and gets them into user hands
- Allows new contributors to have an immediate impact

It describes our methods and practices for:

- Testing and continuous integration
- Organizing, branching, and merging this repository
- Producing and publishing release artifacts
- Documentation
- **TODO**: feature/release planning, ticket assignment, etc

This is a living document that is not (and possibly cannot be)
comprehensive. If something is missing or unclear, or if you have
suggestions for improving our processes, please file an issue or open
a pull request.

# Testing

Cryptol primarily uses golden testing on the Cryptol interpreter
executable. These tests provide the interpreter with input and then
check the output against an expected output file. We make at least one
test for each new issue, and keep the accumulated tests in our suite
as regression tests. The test suite itself is written using the
`test-framework` library, so it can readily output XML for consumption
by CI systems.

## Running tests

To run the test suite, run `./cry test` from the root of the
repository. By default, you'll get output on the console for each test
that fails, either with an explanation for why it failed, or a command
line you can paste in order to compare the test results against the
expected output.

The `./cry test` command invokes the `cryptol-test-runner` executable,
which is defined in the `/tests/` directory. It is invoked with the
location of the `cryptol` executable, an output directory, and
standard `test-framework` command line arguments.

## Creaing a new test

A test consists at minimum of an `.icry` file, which is a batch-mode
file for the interpreter, and an `.icry.stdout` file, which contains
expected output (the "golden" file). As opposed to `.cry` Cryptol
source files, `.icry` files are run by the interpreter line-by-line as
if a user has typed each one in and pressed Enter.

Frequently, one creates an `.icry` file by interactively producing a
desired behavior in the interpreter, and then copying the relevant
lines of input into the file. Remember that, as with unit testing,
golden testing will only test the examples you give it, so make sure
your examples exercise many instances and corner cases of the bug or
feature.

## Expected test failures

We try to keep as few failing tests as possible in the `master`
branch. Usually tests for new features are merged into the `master`
branch in a working state. However if a new bug is reported, we often
write tests for it before it is fixed, particularly if it will take
some time to implement the fix.

To prevent confusion over which tests ought and ought not to be
failing, we add an `.icry.fails` file with an explanatory message
alongside the `.icry` script that defines the test. This will usually
reference an issue number, so that anyone running the test suite will
understand that the reason for the failure is not _their_ changes, but
rather a known issue that is already being handled.

### Example

Issue #6 was a feature request to add let-binding to the
interpreter. @dylanmc gave an example of the input he wanted to be
able to enter, so we created a file `/tests/issues/issue006.icry`
with the contents:

    :let timesTwo x = x * 2
    :let double x = x + x
    :prove \x = timesTwo x == double x

We might not yet know what the expected output should be, so we
created a dummy file `/tests/issues/issue006.icry.stdout`:

    TODO: once implemented, do something sensible here

Since this is not the output we got when running the `.icry` file,
this was now a failing test. To prevent confusion, we marked that it
was expected to fail by putting creating a
`/tests/issues/issue006.icry.fails` file with a reference to the
issue:

    In development, see issue #6

As the issue progressed and we refined the design, @acfoltzer
implemented the `let` feature and came up with some additional
examples that stretch the legs of the feature further, so we updated
our `.icry` file, this time loading a supplemental `.cry` file so we
could test behavior within a module context.

`issue006.cry`:

    f : [32] -> [32]
    f x = x + 2

    g : [32] -> [32]
    g x = f x + 1

`issue006.icry`:

    :l issue006.cry
    g 5
    let f x = 0
    g 5
    (f : [32] -> [32]) 5
    let f x = if (x : [32]) == 0 then 1 else x * (f (x - 1))
    f 5
    let h x = g x
    h 5

Since the feature was now implemented, we could also produce expected
output. The easiest way to do this is to interpret the `.icry` file
using the `-b` flag outside of the test runner, see if the results
look as expected, and then save those results as the new
`.icry.stdout`:

    # start with a fresh build
    % ./cry build
    ...
    # tests are run from within the directory of the .icry file
    % cd tests/issues
    % ../../bin/cryptol -b issue006.icry
    Loading module Cryptol
    Loading module Cryptol
    Loading module Main
    0x00000008
    0x00000008
    0x00000000
    0x00000078
    0x00000008

At this point, it's very important to compare the results you see
against the results you expect from the inputs in the `.icry`
script. Since the results looked correct, we piped the same command
into the matching `.icry.stdout` file and removed the `.icry.fails`
file:

    % ../../bin/cryptol -b issue006.icry.stdout
    % rm issue006.icry.fails

Now the test case `issue006` passes, and will (hopefully!) break if
the let-binding feature breaks.

# Repository organization and practices

The top-level repository directories are:

- `/bench`: Benchmarking executable and suite
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
- `/win32`: Support files for building the Windows installer

## Branching and merging

Within the `GaloisInc/cryptol` repository, we use the
[git-flow model](http://nvie.com/posts/a-successful-git-branching-model/)
for branches and merging. Our version has two notable differences:

1. Our `master` (rather than `develop`) branch serves as the cutting
   edge development branch, and our `release` (rather than `master`)
   branch is where only pristine, tagged releases are committed.

2. We use `wip` (work-in-progress) branches as a centralized storage
   place for (usually individual) work in progress. Whereas a
   `feature` branch is expected to be relatively stable, all bets are
   off with a `wip` branch. Typically `wip` branches are not actually
   merged directly into `master`, but instead are rebased into a new
   branch where the history is cleaned up before merging into
   `master`.

In short:

- Any substantial new features should be developed on a branch
  prefixed with `feature-`, and then merged into `master` when
  completed.
- When we reach a feature freeze for a release, we create a new branch
  prefixed with `release-`, for example `release-2.1.0`. When the
  release is made, we merge those changes back into `master` and make
  a snapshot commit on the `release` branch.
- If a critical bug emerges in already-released software, we create a
  branch off of the relevant `release` branch commit prefixed with
  `hotfix-`. When the hotfix is complete, we merge those changes
  back into `master` and make a snapshot commit on the `release`
  branch.

# Releases

We take the stability and reliability of our releases very
seriously. To that end, our release process is based on principles of
_automation_, _reproducibility_, and _assurance_.

Automation is essential for reducing the possibility of human
error. The checklist for a successful release is fairly lengthy, and
most of the steps need not be done by hand. The real points of
judgment for an individual release are deciding _when_ the codebase is
ready to be released, not _how_ it is released.

Reproducibility is essential for fixing bugs both in hotfixes and
future mainline development. If we cannot reproduce the circumstances
of a release, we might not be able to reproduce bugs that are reported
by users of that release. Bugs are often very particular about the
environment where they will arise, so it is critical to make the
environment of a release consistent.

Assurance is crucial due to the nature of development done with
Cryptol. When people use Cryptol to develop the next generations of
trustworthy systems, we want them to be sure the software was built by
the Cryptol developers, and was not corrupted during download or
replaced by a malicious third party. To this end, we sign our releases
with a [GPG key](http://www.cryptol.net/files/Galois.asc).

## Cutting releases

The release process is:

1. Make sure the `release-n.n.n` branch is in a release/ready state,
   with successful build artifacts across all platforms on the
   relevant GitHub Action.
1. Merge the `release-n.n.n` branch into the pristine `release` branch
   and add a git tag.
1. Merge the `release-n.n.n` branch back into `master` for future
   development.
1. Upload the build archives to the draft release on Github.
1. Upload the `.sig` files to the draft release on Github.
1. Publish the release and announce it

    - <http://www.cryptol.net> (in the `cryptol2-web.git` repo)
    - <cryptol-team@lists.galois.com>
    - <cryptol-users@community.galois.com>
    - @galois on Twitter (for major releases)

# Documentation

There are several overlapping forms of documentation for users of Cryptol:
- the Programming Cryptol book;
- the reference manual; and
- other miscellaneous design docs and changelogs.

These all live in the `docs/` directory.
Some of these forms of documentation, including the book and some of the
design docs, are housed here both in source (LaTeX source code, markdown
files) and compiled (PDF) formats.

Contributors should update the relevant documentation when they modify or
extend user-facing features. Updates should be included in with pull requests
that change the relevant feature. Contributors should re-build any PDFs or
other artifacts when changing the corresponding source code.

## Programming Cryptol
The book lives in `docs/ProgrammingCryptol/`. There's a `Makefile` to build
it. The compiled artifact lives in `docs/ProgrammingCryptol.pdf`; the
`Makefile` does not build to that location, so updated artifacts need to be
copied over. The CI aims to check whether the source and the artifact were
updated in tandem (see `.github/workflows/book.yml`).

## RefMan
The reference manual lives in `docs/RefMan/`. There's a `Makefile` to build
it locally. It's also built by the CI on pull request and deployed to the
website (see `.github/workflows/docs.yml`), which allows users to browse
manual versions corresponding to the `master` branch, any release, and any open
PR. There are no artifacts that need to be manually maintained by contributors.

## Other documentation
There is a variety of other documentation, such as
- The Cryptol preliminaries document (`docs/CryptolPrims.pdf`);
- The Cryptol syntax guide (`docs/Syntax.pdf`);
- The parameterized module guide (`docs/ParameterizedModules/`); and
- other design docs and guides in `docs/`.

Many of these are overlapping with or subsumed by the reference manual and the
book. We recommend that contributors do not build on these documents and
instead focus their efforts on the reference manual and the book. However, if
the source for these is updated, the corresponding PDFs should also be updated
using `pandoc` (see `docs/ParameterizedModules/Makefile` for an example).
