/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias and David Thrane Christiansen
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Commands.Bibliography

import Contents.TeXPrelude
import Authors
import Bibliography
import Contents.Introduction
import Chapters.Noperthedron
import Chapters.Prelims
import Chapters.Cayley
import Chapters.Reduction
import Chapters.Certificates
import Chapters.PolynomialBounds
import Chapters.Data
import Chapters.Main

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

#doc (Manual) "Noperthedron" =>

%%%
shortTitle := "Rupert Counterexample"
authors := ["David Renshaw", "Jason Reed"]
%%%

{include 0 Contents.Introduction}
{include 0 Chapters.Noperthedron}
{include 0 Chapters.Prelims}
{include 0 Chapters.Cayley}
{include 0 Chapters.Reduction}
{include 0 Chapters.Certificates}
{include 0 Chapters.PolynomialBounds}
{include 0 Chapters.Data}
{include 0 Chapters.Main}

{blueprint_graph}

{blueprint_summary}

{blueprint_bibliography}
