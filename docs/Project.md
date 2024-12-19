# Project Files

Cryptol supports specifying a *project* file that can accelerate the repeated
loading and testing of a large, interconnected set of source files. Cryptol
will remember the hashes of the files previously checked and use this to avoid
type-checking and testing files that are unchanged since the previous loading
of the project.

To use this feature a `cryproject.toml` should be created in the root directory
of the cryptol source files.

To check a whole project Cryptol can be invoked with the `--project` or `-p`
flag using the directory containing the project as an argument.

Example:

```shell
cryptol -p myproject/
```

To discard the previous cached results and reload a whole project use
`--refresh-project`. This can be useful when versions of external tools
have changed or simply to get confidence that everything is still in a
working state.

Example:

```shell
cryptol -p myproject/ --refresh-project
```

## `cryproject.toml` Format

Project files are described by a [TOML](https://toml.io/en/) file using the
following top-level key-value assignments:

- `root` can optionally be specified to override the directory that Cryptol
  files are located in.

- `modules` is a list of filenames containing the leaf modules in a project.
  These modules, and all of their dependencies, will be loaded when the project
  is loaded.

Example file:

```toml
modules = [
    "Example/A.cry",
    "Example/B.cry",
]
```

## `loadcache.toml` Format

After loading a project a cache file is generated and stored in
`.cryproject/loadcache.toml`.  This file contains a version number to allow
caches to automatically invalidate when the project subsystem updates.

- `version` specifies the cache file format version in order to allow old
  caches to be invalidated when Cryptol changes the meaning of this file.

- `file` specifies the absolute path to a Cryptol module for those stored
  in files.

- `memory` specifies the module name of a primitive module built into Cryptol.

- `fingerprint` specifies a SHA2-256 hash of the source file which is used to
  detect when the source file has changed from the previous run.

- `foreign_fingerprints` is a list of SHA2-256 hashes of shared libraries that
  this Cryptol file directly includes.

- `include_fingerprints` is a list of SHA2-256 hashes of pre-processor included
  files that this Cryptol files directly includes.

- `docstring_result` is a boolean `true` when `:check-docstrings` previously
  succeeded for this module and `false` when it previously failed. It will be
  missing if tests were never run on this module.

```toml
version = 1

[[modules]]
fingerprint = "2f671b21f2933a006b6a843c7f281388e6b8227f9944b111f87711dc9ca8448f"
foreign_fingerprints = []
include_fingerprints = []
memory = "Cryptol"

[[modules]]
docstring_result = true
file = "/path/to/project/Id.cry"
fingerprint = "a9e6f7a4b65ead6bd8e27442717d6b0dc54afc73e34b18c32f005ceb7a8f3c34"
foreign_fingerprints = [ "c7767a13281a56631c72b9b6f69a17746dc02213e7f2b24a8a4a6fe7afd9ee0a" ]
include_fingerprints = []

[[modules]]
docstring_result = true
file = "/path/to/project/Main.cry"
fingerprint = "6b36f965ebb1a68cf76d689a966806ec879540aa6576a76c1aaa7705a4af09d5"
foreign_fingerprints = []
include_fingerprints = []
```
