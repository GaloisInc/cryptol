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
- **TODO**: documentation
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
by Jenkins and other CI systems.

## Stackage

On the Jenkins machines, we `cp stackage.config cabal.config` before
building in order to build against a Stackage LTS snapshot (updated
periodically). This is to ensure compatibility with downstream
dependencies that rely on Stackage for their stability. We do not have
`cabal.config` in place by default, though, so developers can use
different versions of the compiler.

## Running tests

To run the test suite, run `make test` from the root of the
repository. By default, you'll get output on the console for each test
that fails, either with an explanation for why it failed, or a command
line you can paste in order to compare the test results against the
expected output.

The `make test` target invokes the `cryptol-test-runner` executable,
which is defined in the `/tests/` directory. It is invoked with the
location of the `cryptol` executable, an output directory, and
standard `test-framework` command line arguments. The `test` target in
the `Makefile` provides a template for how to invoke it if you need to
use advanced parameters.

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
    % make
    ...
    # tests are run from within the directory of the .icry file
    % cd tests/issues
    % ../../.cabal-sandbox/bin/cryptol -b issue006.icry
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

    % ../../.cabal-sandbox/bin/cryptol -b issue006.icry.stdout
    % rm issue006.icry.fails

Now the test case `issue006` passes, and will (hopefully!) break if
the let-binding feature breaks.

# Repository organization and practices

The top-level repository directories are:

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
  prefixed with `feature/`, and then merged into `master` when
  completed.
- When we reach a feature freeze for a release, we create a new branch
  prefixed with `release/`, for example `release/2.1.0`. When the
  release is made, we merge those changes back into `master` and make
  a snapshot commit on the `release` branch.
- If a critical bug emerges in already-released software, we create a
  branch off of the relevant `release` branch commit prefixed with
  `hotfix/2.1.1`. When the hotfix is complete, we merge those changes
  back into `master` and make a snapshot commit on the `release`
  branch.

# Releases

We take the stability and reliability of our releases very
seriously. To that end, our release process is based on principles of
_automation_, _reproducibility_, and _assurance_ (**TODO**: assurance
the right word here?).

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
with a [GPG key](http://www.cryptol.net/files/Galois.asc). (**TODO**:
OMG is this really not https?!)

## Cutting releases

**TODO**: make this relevant to folks outside Galois; right now the
 build farm exists within the Galois network only, and Galois also
 controls the release signing key.

The release process is:

1. Make sure the `release/n.n.n` branch is in a release/ready state,
   with successful build artifacts across all platforms on the
   relevant Jenkins job. **TODO**: get a Jenkins job running per
   release branch, rather than just `master`.
1. Merge the `release/n.n.n` branch into the pristine `release` branch
   and add a git tag.
1. Merge the `release/n.n.n` branch back into `master` for future
   development, and delete the `release/n.n.n` branch.
1. Run the `cryptol-release` Jenkins job to create a draft
   release. Specify the build number with the successful artifacts,
   the textual version tag (e.g., "2.1.0"), whether it's a prerelease
   (e.g., an alpha), and keep the `DRAFT` option checked.
1. On the Github page for the draft release and add a changelog
   (**TODO**: how do we generate changelogs?).
1. (**TODO**: this part of the process needs to be better and
   automated) Download the successfully-built artifacts _from
   Jenkins_, and in the same directory run the script
   `/release-infrastructure/sign.sh` from the `cryptol-internal.git`
   repository. You must have the correct GPG key (D3103D7E) for this
   to work.
1. Upload the `.sig` files to the draft release on Github.
1. Publish the release and announce it (**TODO**: compile mailing
   lists, social media outlets, etc where we should make sure to
   announce)
