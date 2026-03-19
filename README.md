# Verso Noperthedron

Standalone Verso Blueprint example project for the Rupert counterexample
development.

## Build

```bash
lake build
```

## Generate

```bash
lake exe blueprint-gen
```

## CI / Pages

```bash
./scripts/ci-pages.sh
```

This matches the included GitHub Actions Pages workflow and checks the rendered
site entry point plus the shared preview manifest under `_out/site/html-multi`.

This repository keeps its committed `VersoBlueprint` dependency pointed at the
official upstream package. Local maintainers can override that dependency
ephemerally during testing.
