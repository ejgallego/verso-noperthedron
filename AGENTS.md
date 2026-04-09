# Leanblueprint To Verso Harness Notes

- This repo uses the local helper at `tools/verso-harness`.
- Keep a root `verso-harness.toml` checked in and treat it as the source of
  truth for package layout, LT chapter scope, and the TeX source path.
- This retrofit keeps the formalization in-tree under `Noperthedron/`; unlike a
  fresh helper consumer, there is no separate formalization submodule here.
- The canonical upstream formalization source of truth is
  `https://github.com/jcreedcmu/Noperthedron` on branch `main`.
- Treat the in-tree `Noperthedron/` directory as a downstream fork that should
  be reconciled against upstream `main`, not as evidence for selecting a
  different upstream branch.
- The canonical TeX blueprint source of truth is vendored under
  `./blueprint/src/chapters/*.tex`.
- Before porting or maintaining blueprint files, read:
  - `tools/verso-harness/references/layout.md`
  - `tools/verso-harness/references/lt-method.md`
  - `tools/verso-harness/references/porting.md`
  - `tools/verso-harness/references/maintenance.md`
  - `tools/verso-harness/references/retrofit.md`
  - `tools/verso-harness/references/beam-validation.md`
- Use `python3 tools/verso-harness/scripts/check_harness.py --project-root .`
  to audit the local harness.
- Treat the legacy TeX or `leanblueprint` source as the prose source of truth.
- Record the real TeX chapter source path for this repo. For this repo it is
  `./blueprint/src/chapters/*.tex`.
- The default deliverable for direct-port chapters is an LT pass. Do not trust
  older LT labels by themselves; every translated informal block now needs an
  adjacent local `tex` witness.
- Preserve section order, paragraph boundaries, labeled theorem order, and
  important dependency edges when translating to Verso.
- Treat the host formalization as the source of truth.
- Prefer `(lean := "...")` links to real declarations rather than duplicating
  Lean code in blueprint modules.
- Preserve TeX `\uses{...}` edges as Verso `{uses "..."}[]` references inside
  the relevant node or proof, not just in free prose.
- When the source block still needs to stay visible, prefer a labeled local
  `tex` block over rewriting it into placeholder prose.
- Treat metadata cleanup as a second phase of LT rather than as a substitute
  for LT.
- Port coherent chapter blocks rather than scattering small edits across
  unrelated chapters.
- Keep shared TeX macros in one `TeXPrelude.lean` module.
- Prefer the harness pattern where `VersoBlueprint` drives the `verso`
  dependency unless this repo has a concrete reason to pin `verso` directly.
- After editing direct-port chapters, run:
  - `python3 tools/verso-harness/scripts/check_lt_source_pairs.py --project-root . <chapter.lean>`
  - `python3 tools/verso-harness/scripts/check_lt_similarity.py --project-root . <chapter.lean>`
- Use `python3 tools/verso-harness/scripts/check_source_label_grounding.py --project-root . <chapter.lean>`
- Use `python3 tools/verso-harness/scripts/lt_audit.py --project-root . <chapter.lean>`
  when you want the source-pair check, similarity report, focused build, and
  optional pages smoke test in one command.
- After a coherent batch, run `bash ./scripts/ci-pages.sh`.
- Keep the root build green. If a Lean link would pull in imports that are not
  harness-clean on the current toolchain, leave the node informal and note the
  dependency in prose instead.
- If using `lean-beam`, avoid parallel `sync` calls against the same project
  root unless the target repo is known to tolerate it.
