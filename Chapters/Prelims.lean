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
