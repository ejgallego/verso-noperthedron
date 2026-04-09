import Verso
import VersoManual
import VersoBlueprint
import Noperthedron.Basic

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Compatibility" =>

:::group "compat_labels"
Compatibility labels retained outside the direct-port chapter set.
:::

:::theorem "thm:polyhedron_radius_def" (lean := "polyhedron_radius_iff") (parent := "compat_labels")
Alias of {uses "thm:polyhedron_radius_iff"}[] used by source-aligned chapter references.
:::
