import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint.git"@"v4.29.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.29.0"

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib Noperthedron where
  roots := #[`Authors, `Contents, `Chapters, `Noperthedron, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
