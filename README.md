# Verso Noperthedron

[![Blueprint Pages](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml/badge.svg)](https://github.com/ejgallego/verso-noperthedron/actions/workflows/blueprint.yml)

This repository is the Verso blueprint harness and integration repo for the
Noperthedron Rupert-counterexample development.

- Upstream formalization source of truth: `Noperthedron/`
- Shared harness: `tools/verso-harness/`
- Harness config: `verso-harness.toml`
- TeX blueprint source of truth: `blueprint/src/chapters/*.tex`

## Pages

- Public site: <https://ejgallego.github.io/verso-noperthedron/>
- Workflow: `.github/workflows/blueprint.yml`
- Local build: `bash ./scripts/ci-pages.sh`
- Local output: `_out/site/html-multi/index.html`

## Build

```bash
lake build
```

## Generate

```bash
lake exe blueprint-gen --output _out/site
```

## Harness Workflow

Use the shared harness docs for retrofit, LT audit, and maintenance:

- `tools/verso-harness/README.md`
- `tools/verso-harness/references/retrofit.md`
- `tools/verso-harness/references/maintenance.md`
- `AGENTS.md`

Common local checks:

```bash
python3 tools/verso-harness/scripts/check_harness.py --project-root .
python3 tools/verso-harness/scripts/check_lt_source_pairs.py --project-root .
python3 tools/verso-harness/scripts/check_lt_similarity.py --project-root .
bash ./scripts/ci-pages.sh
```

## Notes

- Root `lean-toolchain` follows the authoritative upstream formalization line.
- `lakefile.lean` and `lake-manifest.json` are pinned to the matching
  `VersoBlueprint` / mathlib dependency graph for that toolchain.
- Treat `Noperthedron/` as vendored upstream content and prefer syncing from
  upstream `main` over hand-editing it unless explicit downstream patching is
  intended.
