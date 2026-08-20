import Lake
open Lake DSL

require Noperthedron from "./Noperthedron"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint.git" @ "v4.33.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib Contents where
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
