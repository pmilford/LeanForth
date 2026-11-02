# Observed versions

Inventory taken 2026-10-30 on Ubuntu 24.04.4 WSL2 x86-64; details and setup
commands are in `docs/INSTALLATION_LOG.md`.

- Gforth 1.0.0 amd64, locally built; basic invocation tested.
- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb.
- Git 2.43.0; GitHub CLI 2.45.0; GCC 13.3.0; Python 3.13.2.
- Node 24.12.0; npm 11.6.2; Codex 0.166.0.
- `bwrap` not found; Lean sandbox and external checker have not been tested.
- GitHub Actions Smoke run 41120284014 passed on 2026-10-30 for commit
  `44ca571`. It uses Ubuntu's Gforth package, not the pinned local Gforth
  1.0.0 build. GitHub warned that checkout v4 targets deprecated Node 20.

## Pinned downloads (2026-11-02)

`scripts/install-gforth.sh` and `scripts/install-lean.sh` reject downloads
whose SHA-256 differs from these values:

- Gforth 1.0.0 source, `https://net2o.de/gforth-dist/Snapshots/1.0.0/gforth-1.0.0.tar.xz`:
  `79c880b68a4a9aa817b7067c21b79acd5b07149fad78f3f630320db410886fa6`
  (observed 2026-10-30; upstream publishes no authenticated hash).
- Lean 4.35.0 Linux x86-64, `lean-4.35.0-linux.tar.zst` from the GitHub
  `leanprover/lean4` v4.35.0 release:
  `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`
  (the digest GitHub reports for that release asset).
- elan 4.2.4 (`227caca13`, 2026-08-25) manages the local `.tools/elan`
  installation after it was reinstalled on 2026-11-02; the elan version used
  on 2026-10-30 was not recorded.

## CI actions (2026-11-02)

`.github/workflows/ci.yml` pins actions to commit SHAs:
`actions/checkout` v7.0.1 (`3d3c42e5aac5ba805825da76410c181273ba90b1`) and
`actions/cache` v6.1.0 (`55cc8345863c7cc4c66a329aec7e433d2d1c52a9`).
Upgrading from checkout v4 removes the Node 20 deprecation warning.
