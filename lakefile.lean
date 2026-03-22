import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"main"
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.29.0-rc6"
require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint"@"main"

package VersoNoperthedron where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib Noperthedron where
  roots := #[`Authors, `Contents, `Chapters, `Noperthedron, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
