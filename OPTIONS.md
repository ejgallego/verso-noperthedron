# Noperthedron Verso/Blueprint Options

This file is the single source of truth for option policy in `verso-noperthedron`.

## Scope and constraint

`set_option` is file-local during elaboration, so options must be repeated at the top of each chapter file.
There is no import-only centralization for `set_option` without custom metaprogramming.

## Chapter prelude policy

Use this prelude in chapter files unless there is a specific reason not to:

```lean
set_option doc.verso true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0
```

Add chapter-specific options only when needed, for example:

```lean
set_option maxHeartbeats 500000
set_option verso.blueprint.foldProofs true
```

## Current options in use

### Baseline options

- `set_option doc.verso true`
  - Purpose: enable Verso doc elaboration.
  - Used in: all current chapter files.
- `set_option pp.rawOnError true`
  - Purpose: improve diagnostics when elaboration fails.
  - Used in: all current chapter files.
- `set_option verso.code.warnLineLength 0`
  - Purpose: disable long-line warnings for embedded code.
  - Definition: `src/verso-manual/VersoManual/InlineLean/LongLines.lean`.
  - Default: `60`; `0` means disabled.
  - Used in: most chapters.

### Chapter-specific options

- `set_option maxHeartbeats 500000`
  - Purpose: allow larger elaboration budget for heavy chapter content.
  - Used in: `Chapters/Noperthedron.lean`.
- `set_option verso.blueprint.foldProofs true`
  - Purpose: fold proof bodies in Blueprint lean blocks.
  - Definition: `src/VersoBlueprint/Informal/CodeCommon.lean`.
  - Default: `true`.
  - Used in: `Chapters/Noperthedron.lean` (explicit but currently same as default).
- `set_option verso.blueprint.trimTeXLabelPrefix true`
  - Purpose: trim TeX-style prefixes in informal-label-derived Lean names (`thm:foo` -> `foo`) for inline code-block labels.
  - Definition: `src/VersoBlueprint/LabelNameParsing.lean`.
  - Default: `false`.
  - Used in: all chapter files and `Contents.lean` to normalize prefixed inline code labels.

## Coverage snapshot (2026-03-02)

- Has baseline trio (`doc.verso`, `pp.rawOnError`, `verso.code.warnLineLength 0`):
  - `Chapters/Bounding.lean`
  - `Chapters/Computational.lean`
  - `Chapters/GlobalTheorem.lean`
  - `Chapters/LocalTheorem.lean`
  - `Chapters/Main.lean`
  - `Chapters/Noperthedron.lean` (plus chapter-specific options)
  - `Chapters/Rational.lean`
- Missing `verso.code.warnLineLength 0` relative to baseline:
  - `Chapters/Prelims.lean`

## Existing options not currently used in Noperthedron

These already exist in the codebase and can be enabled via `set_option`.

- `linter.verso.manual.headerTags : Bool` (default `false`)
  - File: `src/verso-manual/VersoManual/Linters.lean`
  - Effect: warns on manual headers without permalink tags.
- `linter.typography.quotes : Bool` (default `false`)
  - File: `src/verso/Verso/Linters.lean`
  - Effect: typography suggestions for quote characters.
- `linter.typography.dashes : Bool` (default `false`)
  - File: `src/verso/Verso/Linters.lean`
  - Effect: typography suggestions for en/em dashes.
- `linter.verso.markup.emph : Bool` (default `true`)
  - File: `src/verso/Verso/Linters.lean`
  - Effect: suggests minimizing emphasis markup.
- `linter.verso.markup.code : Bool` (default `true`)
  - File: `src/verso/Verso/Linters.lean`
  - Effect: suggests minimizing inline-code markup.
- `linter.verso.markup.codeBlock : Bool` (default `true`)
  - File: `src/verso/Verso/Linters.lean`
  - Effect: suggests minimizing code-block markup.

## Blueprint options added from backlog (2026-03-02)

These options are now implemented and can be configured with `set_option`.

- `verso.blueprint.profile : Bool` (default `false`)
  - File: `src/VersoBlueprint/Profiling.lean`.
  - Effect: enables timing logs for Blueprint directive/code-block elaboration.
  - Example:
    - `set_option verso.blueprint.profile true`

- `verso.blueprint.externalCode.strictResolve : Bool` (default `false`)
  - File: `src/VersoBlueprint/Informal/ExternalCode.lean`.
  - Effect: unresolved/ambiguous names in `(lean := "...")` become hard errors (instead of warnings + fallback).
  - Current limitation: `(lean := "...")` still uses comma-separated strings as a temporary list workaround.
  - Planned follow-up: remove comma-splitting once Verso supports list arguments for directives.
  - Example:
    - `set_option verso.blueprint.externalCode.strictResolve true`

- `verso.blueprint.trimTeXLabelPrefix : Bool` (default `false`)
  - File: `src/VersoBlueprint/LabelNameParsing.lean`.
  - Effect: trims TeX-style prefixes from informal-label-derived Lean names (`thm:foo` -> `foo`) for inline code labels.
  - Non-effect: does not rewrite `(lean := "...")` external declaration names.
  - Example:
    - `set_option verso.blueprint.trimTeXLabelPrefix true`

- `verso.blueprint.externalCode.previewLimit.type : Nat` (default `1200`)
- `verso.blueprint.externalCode.previewLimit.value : Nat` (default `1200`)
- `verso.blueprint.externalCode.previewLimit.decl : Nat` (default `1600`)
  - File: `src/VersoBlueprint.lean`.
  - Effect: controls truncation limits for external declaration previews.
  - Convention: `0` disables truncation.
  - Example:
    - `set_option verso.blueprint.externalCode.previewLimit.type 800`
    - `set_option verso.blueprint.externalCode.previewLimit.decl 0`

- `verso.blueprint.externalCode.sourceLinkTemplate : String` (default `""`)
  - File: `src/VersoBlueprint/ExternalRefSnapshot.lean`.
  - Effect: enables optional source links for external declarations.
  - Placeholders: `{path}`, `{relpath}`, `{module}`, `{line}`, `{column}`.
  - Convention: empty string disables source-link generation.
  - Example:
    - `set_option verso.blueprint.externalCode.sourceLinkTemplate "https://github.com/<org>/<repo>/blob/main/{relpath}#L{line}"`

- `verso.blueprint.graph.defaultDirection : String` (default `"TB"`)
  - File: `src/VersoBlueprint/Commands/Graph.lean`.
  - Effect: default graph direction for `blueprint_graph` when no `(direction := ...)` is passed.
  - Accepted values: `LR`, `RL`, `TB`, `BT` (case-insensitive, plus aliases like `left-right`).
  - Example:
    - `set_option verso.blueprint.graph.defaultDirection "LR"`

## Remaining backlog

1. Decide whether to make `Chapters/Prelims.lean` adopt `set_option verso.code.warnLineLength 0` for full consistency.
