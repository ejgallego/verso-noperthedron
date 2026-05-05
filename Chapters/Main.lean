/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import Noperthedron.ProofOfMainTheorem

open Verso.Genre Manual Informal
open Noperthedron

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Main Theorems" =>

:::group "main_tight_interval"
No Rupert solution on the certified tight interval.
:::

:::group "main_pose_reductions"
Reductions from general poses to certified subcases.
:::

:::group "main_final_nonrupert"
Final non-Rupert conclusions for the noperthedron.
:::

:::theorem "thm:no_nopert_tight_pose" (lean := "no_nopert_tight_pose") (parent := "main_tight_interval")
Using {uses "def:noperthedron"}[].

There does not in fact exist a noperthedron Rupert solution with

$$`
\begin{align*}
\theta_1,\theta_2&\in[0,2\pi/15] \subset [0,0.42], \\
\varphi_1&\in [0,\pi] \subset [0,3.15],\\
\varphi_2&\in [0,\pi/2] \subset [0,1.58],\\
\alpha &\in [-\pi/2,\pi/2] \subset [-1.58,1.58].
\end{align*}
`
:::

```tex
\begin{theorem}
\label{thm:no_nopert_tight_pose}
\lean{no_nopert_tight_pose}
\uses{def:noperthedron}
\leanok
There does not in fact exist a noperthedron Rupert solution with
\begin{align*}
\theta_1,\theta_2&\in[0,2\pi/15] \subset [0,0.42], \\
\varphi_1&\in [0,\pi] \subset [0,3.15],\\
\varphi_2&\in [0,\pi/2] \subset [0,1.58],\\
\alpha &\in [-\pi/2,\pi/2] \subset [-1.58,1.58].
\end{align*}
\end{theorem}
```

:::proof "thm:no_nopert_tight_pose"
Using {uses "thm:exists_solution_table"}[] and {uses "thm:row_valid_imp_not_rupert"}[].

By {uses "thm:exists_solution_table"}[this theorem], there is a valid solution table
containing a valid row whose pose interval is a superset of
the 5-dimensional interval above. By {uses "thm:row_valid_imp_not_rupert"}[this theorem],
there is no Rupert solution in that interval.
:::

```tex
\begin{proof}
\leanok
\uses{thm:exists_solution_table,thm:row_valid_imp_not_rupert}
By \ref{thm:exists_solution_table}, there is a valid solution table
containing a valid row whose pose interval is a superset of
the 5-d interval above. By \ref{thm:row_valid_imp_not_rupert}, this means
there is no Rupert solution in that interval.
\end{proof}
```

:::theorem "thm:no_nopert_pose" (lean := "no_nopert_pose") (parent := "main_pose_reductions")
There is no 5-parameter pose that makes the noperthedron have the Rupert property.
:::

```tex
\begin{theorem}
\label{thm:no_nopert_pose}
\lean{no_nopert_pose}
\leanok
There is no 5-parameter pose that makes the noperthedron have the Rupert property.
\end{theorem}
```

:::proof "thm:no_nopert_pose"
Using {uses "thm:no_nopert_tight_pose"}[] and {uses "cor:rupert_tightening"}[].

Theorem {uses "thm:no_nopert_tight_pose"}[] says there is no tight pose
that makes the noperthedron Rupert. Corollary {uses "cor:rupert_tightening"}[]
says that this suffices for the general case.
:::

```tex
\begin{proof}
\uses{thm:no_nopert_tight_pose, cor:rupert_tightening}
\leanok
Theorem~\ref{thm:no_nopert_tight_pose} says there is no tight pose
that makes the noperthedron Rupert. Corollary~\ref{cor:rupert_tightening}
says that this suffices for the general case.
\end{proof}
```

:::theorem "thm:no_nopert_rot_pose" (lean := "no_nopert_rot_pose") (parent := "main_pose_reductions")
There is no purely rotational pose that makes the noperthedron have the Rupert property.
:::

```tex
\begin{theorem}
\label{thm:no_nopert_rot_pose}
\lean{no_nopert_rot_pose}
\leanok
There is no purely rotational pose that makes the noperthedron have the Rupert property.
\end{theorem}
```

:::proof "thm:no_nopert_rot_pose"
Using {uses "thm:pose_of_matrix_pose"}[] and {uses "thm:no_nopert_pose"}[].

Suppose there were a purely rotational pose. Then convert that to an equivalent
5-parameter pose with Theorem {uses "thm:pose_of_matrix_pose"}[] and
appeal to Theorem {uses "thm:no_nopert_pose"}[].
:::

```tex
\begin{proof}
\uses{thm:pose_of_matrix_pose, thm:no_nopert_pose}
\leanok
Suppose there were a purely rotational pose. Then convert that to an equivalent 5-parameter pose
with Theorem~\ref{thm:pose_of_matrix_pose} and
appeal to Theorem~\ref{thm:no_nopert_pose}.
\end{proof}
```

:::theorem "thm:no_nopert_matrix_pose" (lean := "no_nopert_matrix_pose") (parent := "main_pose_reductions")
There is no pose that makes the noperthedron have the Rupert property.
:::

```tex
\begin{theorem}
\label{thm:no_nopert_matrix_pose}
\lean{no_nopert_matrix_pose}
\leanok
There is no pose that makes the noperthedron have the Rupert property.
\end{theorem}
```

:::proof "thm:no_nopert_matrix_pose"
Using {uses "lemma:nopert_point_symmetric"}[], {uses "thm:no_nopert_rot_pose"}[], and {uses "thm:rupert_implies_rot_rupert"}[].

By Theorem {uses "thm:rupert_implies_rot_rupert"}[], we need only show that the noperthedron
is pointsymmetric to see that if it is Rupert, then it must be Rupert via a purely rotational pose.
But Lemma {uses "lemma:nopert_point_symmetric"}[] shows exactly this. And yet we know via
Theorem {uses "thm:no_nopert_rot_pose"}[] that the noperthedron is not rotationally Rupert, so we have
a contradiction, hence the noperthedron has no pose that makes it Rupert.
:::

```tex
\begin{proof}
\uses{lemma:nopert_point_symmetric, thm:no_nopert_rot_pose, thm:rupert_implies_rot_rupert}
\leanok
By Theorem~\ref{thm:rupert_implies_rot_rupert}, we need only show that the noperthedron
is pointsymmetric to see that if it is Rupert, then it must be Rupert via a purely rotational pose.
But Lemma~\ref{lemma:nopert_point_symmetric} shows exactly this. And yet we know via
Theorem~\ref{thm:no_nopert_rot_pose} that the noperthedron is not rotationally Rupert, so we have
a contradiction, hence the noperthedron has no pose that makes it Rupert.
\end{proof}
```

:::theorem "thm:nopert_not_rupert_set" (lean := "nopert_not_rupert_set") (parent := "main_final_nonrupert")
Using {uses "def:noperthedron"}[].

The noperthedron is not a Rupert set.
:::

```tex
\begin{theorem}
\uses{def:noperthedron}
\label{thm:nopert_not_rupert_set}
\lean{nopert_not_rupert_set}
\leanok
The noperthedron is not a Rupert set.
\end{theorem}
```

:::proof "thm:nopert_not_rupert_set"
Using {uses "thm:no_nopert_matrix_pose"}[].

By Theorem {uses "thm:no_nopert_matrix_pose"}[], there is no pose that makes the noperthedron a Rupert set.
:::

```tex
\begin{proof}
\uses{thm:no_nopert_matrix_pose}
\leanok
By Theorem~\ref{thm:no_nopert_matrix_pose}, there is no pose that makes the noperthedron a Rupert set.
\end{proof}
```

:::theorem "thm:nopert_not_rupert" (lean := "nopert_not_rupert") (parent := "main_final_nonrupert")
The noperthedron is not a Rupert polyhedron.
:::

```tex
\begin{theorem}
\label{thm:nopert_not_rupert}
\lean{nopert_not_rupert}
\leanok
The noperthedron is not a Rupert polyhedron.
\end{theorem}
```

:::proof "thm:nopert_not_rupert"
Using {uses "thm:rupert_iff_rupert_set"}[] and {uses "thm:nopert_not_rupert_set"}[].

By {uses "thm:rupert_iff_rupert_set"}[], it suffices to show that the convex hull of
noperthedron vertices is not a Rupert set, which is exactly
{uses "thm:nopert_not_rupert_set"}[the previous theorem].
:::

```tex
\begin{proof}
\leanok
\uses{thm:rupert_iff_rupert_set, thm:nopert_not_rupert_set}
By Theorem~\ref{thm:rupert_iff_rupert_set} it suffices to show that the convex hull of
the noperthedron vertices is not a Rupert set. But this is exactly what Theorem~\ref{thm:nopert_not_rupert_set} shows.
\end{proof}
```
