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

This repository keeps its committed `VersoBlueprint` dependency pointed at the
official upstream package. Local maintainers can override that dependency with
Lake package overrides for ephemeral testing.
