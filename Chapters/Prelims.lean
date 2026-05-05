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
import Noperthedron.Vertices.Exact

open Verso.Genre Manual Informal
open Noperthedron

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

#doc (Manual) "Preliminaries" =>

TODO: This whole chapter needs organization, it's just a grab bag of miscellaneous results for now.

```tex
TODO: This whole chapter needs organization, it's just a grab bag of miscellaneous results for now.
```

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

```tex
\begin{theorem}[Rupert Polyhedron iff Rupert Set]
\label{thm:rupert_iff_rupert_set}
\lean{rupert_iff_rupert_set}
\leanok
The following are equivalent:
\begin{itemize}
\item The convex polyhedron with vertex set $v$ is Rupert.
\item The convex closure of $v$ is a Rupert set.
\end{itemize}
\end{theorem}
```

:::proof "thm:rupert_iff_rupert_set"
TODO: import this from the other repo
:::

```tex
\begin{proof}
\leanok
TODO: import this from the other repo
\end{proof}
```

# Poses

TODO

```tex
TODO
```

:::theorem "thm:pose_of_matrix_pose" (lean := "pose_of_matrix_pose,converted_pose_rupert_iff") (parent := "prelims_pose_reduction")
Given a pose with zero offset, there exists a 5-parameter pose that is equivalent to it.
:::

```tex
\begin{theorem}
\label{thm:pose_of_matrix_pose}
\lean{pose_of_matrix_pose, converted_pose_rupert_iff}
\leanok
Given a pose with zero offset, there exists a 5-parameter pose that is equivalent to it.
\end{theorem}
```

:::proof "thm:pose_of_matrix_pose"
By putting the pose into a canonical form as a Z rotation followed by a Y followed by a Z.
:::

```tex
\begin{proof}
By putting the pose into a canonical form as a Z rotation followed by a Y followed by a Z.
\leanok
\end{proof}
```

# Pointsymmetry and Rupertness

:::theorem "thm:rupert_implies_rot_rupert" (lean := "rupert_implies_rot_rupert") (parent := "prelims_pointsymmetry_reduction")
If a set is point symmetric and convex, then it being Rupert implies
it being purely rotationally Rupert.
:::

```tex
\begin{theorem}
\label{thm:rupert_implies_rot_rupert}
\lean{rupert_implies_rot_rupert}
\leanok
If a set is point symmetric and convex, then it being Rupert implies
it being purely rotationally Rupert.
\end{theorem}
```

:::proof "thm:rupert_implies_rot_rupert"
TODO: informalize proof
:::

```tex
\begin{proof}
\leanok
TODO: informalize proof
\end{proof}
```

:::theorem "thm:polyhedron_radius_iff" (lean := "Polyhedron.radius_iff") (parent := "prelims_radius_tools")
Suppose $`S` is a finite set of points in $`\R^n`.
The radius of the polyhedron $`S` is $`r` iff
- there is a vector $`v \in S` with $`\|v\| = r`
- all vectors $`v \in S` have $`\|v\| \le r`
:::

```tex
\begin{theorem}
\label{thm:polyhedron_radius_iff}
\lean{Polyhedron.radius_iff}
\leanok
Suppose $S$ is a finite set of points in $\R^n$.
The radius of the polyhedron $S$ is $r$ iff
\begin{itemize}
\item there is a vector $v \in S$ with $\|v\| = r$
\item all vectors $v \in S$ have $\|v\| \le r$
\end{itemize}
\end{theorem}
```

:::proof "thm:polyhedron_radius_iff"
Immediate from definition.
:::

```tex
\begin{proof}
\leanok
Immediate from definition.
\end{proof}
```

:::theorem "thm:pointsymmetrize_pres_radius" (parent := "prelims_radius_tools")
Pointsymmetrization preserves radius.
:::

```tex
\begin{theorem}
\label{thm:pointsymmetrize_pres_radius}
\lean{pointsymmetrize_pres_radius}
\leanok
Pointsymmetrization preserves radius.
\end{theorem}
```

:::proof "thm:pointsymmetrize_pres_radius"
{uses "thm:polyhedron_radius_iff"}[]

Because the reflection of a point about the origin preserves its norm.
:::

```tex
\begin{proof}
\uses{thm:polyhedron_radius_iff}
\leanok
Because the reflection of a point about the origin preserves its norm.
\end{proof}
```
