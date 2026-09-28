# Releasing

**Merging is not releasing.** Anything merged to `main` sits unpublished until
a release is cut. Releases are cut by merging a **Release PR** that
[release-plz](https://release-plz.dev) keeps up to date for you.

## What this means for contributors

1. **Never edit `version =` in `Cargo.toml`.** Versions are assigned by the
   Release PR, not by a feature PR.
2. **Write a conventional-commit PR title** (`feat: …`, `fix: …`, `feat!: …`
   for a breaking change). A squash merge makes the PR title the commit
   subject, and the changelog is generated from those subjects.

## One-time setup

The release job authenticates to crates.io via
[Trusted Publishing](https://crates.io/docs/trusted-publishing) (OIDC, no
long-lived token in this repository). Before the first release, on crates.io
under this crate's Settings -> Trusted Publishing, add:

- Repository owner: `OpenVTC`
- Repository name: `predicate-credential-system`
- Workflow filename: `publish.yml`
- Environment: `crates-io`

Until that exists, `release-plz-release` fails at the authentication step,
naming exactly this.
