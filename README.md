# Verso Noperthedron

[![Blueprint Pages](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml/badge.svg)](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml)

Verso Blueprint port of the Noperthedron Blueprint, with the upstream
[`Noperthedron`](Noperthedron/) formalization carried locally as a submodule.

Blueprint: <https://ejgallego.github.io/verso-noperthedron/>

This repo follows the upstream blueprint strictly and translates its source
markup language to Verso with the help of AI.

## Build

```bash
lake build
```

## Generate

```bash
lake env lean --run Main.lean --output _out/site
```

This repository follows the shared
[`tools/verso-harness`](tools/verso-harness/) workflow. The root
[`lean-toolchain`](lean-toolchain) matches the upstream formalization, and
[`lakefile.lean`](lakefile.lean) pins `VersoBlueprint` to the matching release
branch.
