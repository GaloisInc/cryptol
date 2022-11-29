# Cryptol Python Client

In-development Python client for Cryptol. Currently tested on Linux and MacOS --
at present there may be some minor issues running the Python Client in a Windows
environment that need to be addressed (e.g., some Python process management methods
are not cross-OS-compatible).

This Cryptol client depends on the
[cryptol-remote-api](https://github.com/GaloisInc/cryptol/tree/master/cryptol-remote-api)
server.

# TL;DR Steps to running Cryptol Python scripts

1. Clone the repo 
```
git clone https://github.com/GaloisInc/cryptol.git
```
2. Enter the repo
```
cd cryptol
```
3. Initialize git submodules 
```
git submodule update --init
```
4. Navigate to the python client
```
cd cryptol-remote-api/python
```
5. Install and setup some version of the `cryptol-remote-api` server and update any
   relevant environment variables as needed (see `cryptol.connect()` documentation
   for the various ways a server can be connected to).
   E.g., here is how the docker image of the server might be used:
```
$ docker run --name=cryptol-remote-api -d \
  -v $PWD/tests/cryptol/test-files:/home/cryptol/tests/cryptol/test-files \
  -p 8080:8080 \
  ghcr.io/galoisinc/cryptol-remote-api:nightly-portable
$ export CRYPTOL_SERVER_URL="http://localhost:8080/"
```
6. Install the Python client (requires Python v3.7 or newer -- we recommend using [`poetry`](https://python-poetry.org/docs/#installation) to install the package):
```
$ poetry install 
```
7. Run tests or individual scripts:
```
$ poetry run python -m unittest discover tests/cryptol
$ poetry run python tests/cryptol/test_salsa20.py
```

# Python Client Installation (via Poetry)

First, clone the repository and submodules.

```
$ git clone https://github.com/GaloisInc/cryptol.git
$ cd cryptol
$ git submodule update --init
```

Then, use [`poetry`](https://python-poetry.org/docs/#installation) to install
the python client from the `cryptol-remote-api/python` directory:

```
$ cd cryptol-remote-api/python
$ poetry install
```

# Cryptol server

To run the verification scripts a `cryptol-remote-api` server must be available,
either as a local executable or running in docker image listening on a port.

## Connecting with a server in a script

Connecting to a server in a Python script is accomplished via the `cryptol.connect`
method. Its accompanying Python doc strings describe the various ways it can be
used. Below is a brief summary:

`cryptol.connect()`, when provided no arguments, will attempt the following in order:

1. If the environment variable ``CRYPTOL_SERVER`` is set and refers to an
   executable, it is assumed to be a `cryptol-remote-api` executable and will be
   used for the duration of the script.
2. If the environment variable ``CRYPTOL_SERVER_URL`` is set, it is assumed to be
   the URL for a running Cryptol server in ``http`` mode and will be connected to.
   (N.B., this can be a local server or a server running in a docker image.)
3. If an executable ``cryptol-remote-api`` is available on the ``PATH`` it is
    assumed to be a Cryptol server and will be used for the duration of the script.

Additional arguments and options are documented with the function.

Notably, the `reset_server` keyword can be used to connect to a running server
and reset it, ensuring states from previous scripts have been cleared. E.g.,
`cryptol.connect(reset_server=True)`.


## Acquiring a Cryptol Server

There are several ways a server executable can be obtained.

### Server executables

An executable of the server is now included in each release of Cryptol.

Nightly server builds can be found as `Artifacts` of the [Nightly
Builds](https://github.com/GaloisInc/saw-script/actions/workflows/nightly.yml)
github action. I.e., go to the `Nightly Builds` Github Action, click on a
successful build, scroll to the bottom and under `Artifacts` a Linux, Windows,
and MacOS tarball will be listed.

Nightly Docker images of the server can be found under the
[Packages](https://github.com/orgs/GaloisInc/packages?repo_name=cryptol) section
of the Cryptol github repository.

### Server docker images

Release docker images for the Cryptol server are distributed with Cryptol
releases; nightly Cryptol servers are available under the
[Packages](https://github.com/orgs/GaloisInc/packages) section of the Cryptol repository.

These images are set up to run as HTTP `cryptol-remote-api` servers, e.g.:

```
docker run --name=cryptol-remote-api -d \
  -p 8080:8080 \
  ghcr.io/galoisinc/cryptol-remote-api:nightly-portable
```

The `-v` option to `docker run` can be used to load files into the docker
server's working directory so they can be loaded into the server at the request
of python scripts. E.g., `-v PATH_TO_FILES:/home/cryptol/files/` will upload the
contents of the host machine's directory `PATH_TO_FILES` to the
`/home/cryptol/files/` directory in the docker container, which corresponds to the
relative path `files/` for the Cryptol server. (If desired, it can be useful to
place files in a location in the Docker container such that the same relative
paths in scripts refer to the same files in the host machine and docker
container.)

### Building from Source

If this repository is checked out and the build directions are successfully run,
`cabal v2-exec which cryptol-remote-api` should indicate where the server executable has
been stored by `cabal`.

Alternatively `cabal v2-install cryptol-remote-api` should install the server
executable into the user's `~/.cabal/bin` directory (or similar), which (if
configured properly) should then appear as `cryptol-remote-api` in a user's `PATH`.


# Running Python Cryptol scripts

Once the server is setup and any path variables are setup as desired, the
Python (>= v3.7) client can be installed using
[`poetry`](https://python-poetry.org/docs/#installation) as follows:

```
$ cd cryptol-remote-api/python
$ poetry install
```

Then the tests or individual scripts can be run as follows:
```
$ poetry run python -m unittest discover tests/cryptol
$ poetry run python tests/cryptol/test_cryptol_api.py
```

If leveraging environment variables is undesirable, the scripts themselves can
specify a command to launch the server, e.g.:

```
cryptol.connect(COMMAND)
```

where `COMMAND` is a command to launch a new Cryptol server in socket mode.

Or a server URL can be specified directly in the script, e.g.:

```
cryptol.connect(url=URL)
```

There is a step-by-step example [here](GettingStarted.md).

## Running Cryptol Scripts from a clean server state

To ensure any previous server state is cleared when running a Cryptol Python script
against a persistent server (e.g., one running in HTTP mode in a different process),
the `reset_server` keyword can be passed to `cryptol.connect()`. E.g.,

```
cryptol.connect(url="http://localhost:8080/", reset_server=True)
```

will connect to a Cryptol server running at `http://localhost:8080/` and will
guarantee any previous state on the server is cleared.
