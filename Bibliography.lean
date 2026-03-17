/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias and David Thrane Christiansen
-/

import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre.Manual.Bibliography

@[bib "polyhedron.without.rupert"]
def polyhedron.without.rupert : Citable := .arXiv
    { title := inlines!"A convex polyhedron without Rupert's property"
    , authors := #[inlines!"Jakob Steininger", inlines!"Sergey Yurkevich"]
    , year := 2025
    , id := "polyhedron.without.rupert"
    }
