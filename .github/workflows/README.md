# GitHub Actions workflows

The workflows in this directory are split into event-triggered entry points and
reusable workflows called by the main CI workflow.

## CI workflow dependencies

```text
ci.yml
├── config
├── platform matrix (after config)
│   └── ci-platform.yml
│       ├── ci-build.yml
│       └── ci-test.yml (after build, using its artifacts)
└── ci-images.yml (after config, for scheduled, manual, and release builds)
```

Each platform in the matrix is processed independently. Tests for a platform
can therefore start as soon as that platform's build artifacts are available.
The Docker image workflow does not depend on any platform build.

## Event-triggered workflows

### `ci.yml`

The main Cryptol CI entry point. It runs on pull requests, selected branches
and tags, a daily schedule, and manual dispatches. Its `config` job determines
the version, release status, event type, artifact name, and retention period.
It then invokes `ci-platform.yml` for each platform matrix entry and invokes
`ci-images.yml` when Docker images should be built.

This workflow has no caller-supplied parameters.

### `docs.yml`

Builds the Cryptol documentation on pull requests, selected branches and tags,
and manual dispatches. It also assembles and deploys the versioned GitHub Pages
site when running in the main repository. Its two jobs are independent and may
run in parallel.

This workflow has no caller-supplied parameters.

### `book.yml`

Runs on pull requests and checks that the checked-in "Programming Cryptol" PDF
was updated.  We only do this if its source files changed.

This workflow has no caller-supplied parameters.

## Reusable CI workflows

All inputs below are required.

### `ci-platform.yml`

Coordinates the build and tests for one platform. It calls `ci-build.yml`,
waits for that build to finish, and then calls `ci-test.yml` when `test-kind`
is `test-lib` or `full`.

| Input                | Type   | Description                                                    |
| -------------------- | ------ | -------------------------------------------------------------- |
| `os`                 | string | GitHub-hosted runner label.                                    |
| `ghc-version`        | string | GHC version used for the build.                                |
| `cabal`              | string | Cabal version used for the build.                              |
| `test-kind`          | string | Test selection: `none`, `test-lib`, or `full`.                 |
| `solver-pkg-version` | string | What4 solver package release or snapshot.                      |
| `name`               | string | Base name for distribution artifacts.                          |
| `version`            | string | Cryptol version being built.                                   |
| `release`            | string | Whether this is a release build (`true` or `false`).           |
| `event-tag`          | string | Whether the triggering ref is a tag (`true` or `false`).       |
| `retention-days`     | number | Artifact retention period.                                     |

It also accepts and forwards the optional Apple and GPG signing secrets listed
under `ci-build.yml`.

The `test-kind` input controls which tests, if any, run after that build:

- `none`: Do not upload test artifacts or run tests.
- `test-lib`: Run the test groups discovered under `tests/`.
- `full`: Run the `test-lib` groups, the Haskell `cryptol-api-tests` suite,
  and the Python integration tests for the Remote API and eval server.

### `ci-build.yml`

Builds Cryptol on one platform, performs platform-specific signing and
packaging, and uploads distributions. When tests are requested, it additionally
uploads the executables and solver binaries consumed by `ci-test.yml`.

Its inputs are the same as those for `ci-platform.yml`.

Optional secrets:

- `APPLE_P12_CERTIFICATE`
- `APPLE_P12_PASSWORD`
- `APPLE_P12_IDENTITY_NAME`
- `APPLE_P8_KEY_ID`
- `APPLE_P8_ISSUER_ID`
- `APPLE_P8_API_KEY`
- `SIGNING_PASSPHRASE`
- `SIGNING_KEY`

### `ci-test.yml`

Discovers and runs the test groups for one platform. It depends on the
`${os}-dist-bin` and `${os}-bin` artifacts uploaded by `ci-build.yml`.

| Input       | Type   | Description                                             |
| ----------- | ------ | ------------------------------------------------------- |
| `os`        | string | GitHub-hosted runner label and build-artifact prefix.   |
| `test-kind` | string | Test selection: `test-lib` or `full`.                   |


### `ci-images.yml`

Builds the Cryptol and Cryptol Remote API Docker images. It manages build
caches, tests the Remote API image and Helm chart, and publishes nightly or
release tags when appropriate. It is independent of the platform build and
test workflows.

| Input            | Type   | Description                                        |
| ---------------- | ------ | -------------------------------------------------- |
| `version`        | string | Version used for a release image tag.              |
| `release`        | string | Whether to publish versioned and `latest` tags.    |
| `event-schedule` | string | Whether to publish the `nightly` tag.              |
