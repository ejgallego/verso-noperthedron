/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet
import Noperthedron.ConvertPose
import Noperthedron.CommonCenter
import Noperthedron.Nopert

open Verso.Genre Manual Informal

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

#doc (Manual) "Preliminaries" =>

TODO: This whole chapter needs organization, it's just a grab bag of miscellaneous results for now.

:::group "prelims_rupert_equiv"
Equivalence between Rupert polyhedra and Rupert sets.
:::

:::group "prelims_pose_reduction"
Pose normalization and reduction lemmas.
:::

:::group "prelims_pointsymmetry_reduction"
Pointsymmetry reduction to rotational Rupert poses.
:::

:::group "prelims_radius_tools"
Radius characterization and preservation tools.
:::

# Rupert Sets

:::theorem "thm:rupert_iff_rupert_set" (lean := "rupert_iff_rupert_set") (parent := "prelims_rupert_equiv")
The following are equivalent:
- The convex polyhedron with vertex set $`v` is Rupert.
- The convex closure of $`v` is a Rupert set.
:::

:::proof "thm:rupert_iff_rupert_set" (leanok := true)
TODO: import this from the other repo
:::

# Poses

TODO

:::theorem "thm:pose_of_matrix_pose" (lean := "pose_of_matrix_pose,converted_pose_rupert_iff") (parent := "prelims_pose_reduction")
Given a pose with zero offset, there exists a 5-parameter pose that is equivalent to it.
:::

:::proof "thm:pose_of_matrix_pose" (leanok := true)
By putting the pose into a canonical form as a Z rotation followed by a Y followed by a Z.
:::

# Pointsymmetry and Rupertness

:::theorem "thm:rupert_implies_rot_rupert" (lean := "rupert_implies_rot_rupert") (parent := "prelims_pointsymmetry_reduction")
If a set is point symmetric and convex, then it being Rupert implies
it being purely rotationally Rupert.
:::

:::proof "thm:rupert_implies_rot_rupert" (leanok := true)
TODO: informalize proof
:::

:::theorem "thm:polyhedron_radius_iff" (lean := "polyhedron_radius_iff") (parent := "prelims_radius_tools")
Suppose $`S` is a finite set of points in $`\mathbb{R}^n`.
The radius of the polyhedron $`S` is $`r` iff:
- there is a vector $`v \in S` with $`\|v\| = r`
- all vectors $`v \in S` have $`\|v\| \le r`
:::

:::proof "thm:polyhedron_radius_iff" (leanok := true)
Immediate from definition.
:::

:::theorem "thm:polyhedron_radius_def" (lean := "polyhedron_radius_iff") (parent := "prelims_radius_tools")
Alias of {uses "thm:polyhedron_radius_iff"}[] used in the original TeX source.
:::

:::proof "thm:polyhedron_radius_def" (leanok := true)
Immediate from {uses "thm:polyhedron_radius_iff"}[].
:::

:::theorem "thm:pointsymmetrize_pres_radius" (lean := "pointsymmetrize_pres_radius") (parent := "prelims_radius_tools")
Pointsymmetrization preserves radius.
:::

:::proof "thm:pointsymmetrize_pres_radius" (leanok := true)
Using {uses "thm:polyhedron_radius_iff"}[].
Because the reflection of a point about the origin preserves its norm.
:::
