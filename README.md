# Verso Noperthedron

[![Blueprint Pages](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml/badge.svg)](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml)

Verso Blueprint port of the Noperthedron Blueprint. The upstream formalization
is carried locally as the [`Noperthedron`](Noperthedron/) submodule.

Blueprint: <https://ejgallego.github.io/verso-noperthedron/>
Upstream blueprint repository:
[jcreedcmu/Noperthedron](https://github.com/jcreedcmu/Noperthedron)

This repo follows the upstream blueprint strictly and translates its source
markup language to Verso with the help of AI. Credit for the original blueprint
and formalization belongs to the upstream project.

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
