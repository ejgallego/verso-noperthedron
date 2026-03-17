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

import Authors
import Bibliography
import Chapters.Noperthedron
import Chapters.Bounding
import Chapters.Prelims
import Chapters.GlobalTheorem
import Chapters.LocalTheorem
import Chapters.Rational
import Chapters.Computational
import Chapters.Main

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

#doc (Manual) "Contents" =>

%%%
shortTitle := "Rupert Counterexample"
authors := ["David Renshaw", "Jason Reed"]
%%%

# Introduction

We follow for the most part the structure of {citet polyhedron.without.rupert}[].

{include 0 Chapters.Noperthedron}
{include 0 Chapters.Bounding}
{include 0 Chapters.Prelims}
{include 0 Chapters.GlobalTheorem}
{include 0 Chapters.LocalTheorem}
{include 0 Chapters.Rational}
{include 0 Chapters.Computational}
{include 0 Chapters.Main}

{blueprint_graph}

{bp_summary}

{bp_bibliography}
