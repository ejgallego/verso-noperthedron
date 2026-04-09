import Verso
import VersoManual
import VersoBlueprint
import Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

We follow for the most part the structure of {citet polyhedron.without.rupert}[].
