import Lake
open Lake DSL

require Noperthedron from "./Noperthedron"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint.git" @ "v4.31.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`verso.blueprint.math.lint, true⟩,
    ⟨`verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib Contents where
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
