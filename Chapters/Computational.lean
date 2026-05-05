/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Verso
import VersoManual
import VersoBlueprint
import Bibliography
import Macros
import Noperthedron.ComputationalStep
import Noperthedron.SolutionTable

open Verso.Genre Manual Informal
open Noperthedron

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Computational Step" =>

:::group "computational_table_construction"
Construction of the certified interval solution table.
:::

:::group "computational_table_soundness"
Soundness of table rows and propagated non-Rupert certificates.
:::

:::theorem "thm:exists_solution_table" (lean := "exists_solution_table") (parent := "computational_table_construction")
There exists a valid solution table whose zeroth row covers

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
\lean{exists_solution_table}
\leanok
\label{thm:exists_solution_table}
There exists a valid solution table whose zeroth row covers
\begin{align*}
\theta_1,\theta_2&\in[0,2\pi/15] \subset [0,0.42], \\
\varphi_1&\in [0,\pi] \subset [0,3.15],\\
\varphi_2&\in [0,\pi/2] \subset [0,1.58],\\
\alpha &\in [-\pi/2,\pi/2] \subset [-1.58,1.58].
\end{align*}
\end{theorem}
```

:::proof "thm:exists_solution_table"
By exhibiting the table and running the validity checking algorithm.
:::

```tex
\begin{proof}
By exhibiting the table and running the validity checking algorithm.
\end{proof}
```

:::theorem "thm:solution_global" (lean := "Solution.valid_global_imp_no_rupert") (parent := "computational_table_soundness")
If a global node in the solution tree is valid, then there is no Rupert solution for its interval.
:::

```tex
\begin{theorem}
\label{thm:solution_global}
If a global node in the solution tree is valid, then there is no Rupert solution for its interval.
\leanok
\lean{Solution.valid_global_imp_no_rupert}
\end{theorem}
```

:::proof "thm:solution_global"
{uses "thm:global_rational"}[]
:::

```tex
\begin{proof}
\uses{thm:global_rational}
\end{proof}
```

:::theorem "thm:solution_local" (lean := "Solution.valid_local_imp_no_rupert") (parent := "computational_table_soundness")
If a local node in the solution tree is valid, then there is no Rupert solution for its interval.
:::

```tex
\begin{theorem}
\label{thm:solution_local}
If a local node in the solution tree is valid, then there is no Rupert solution for its interval.
\leanok
\lean{Solution.valid_local_imp_no_rupert}
\end{theorem}
```

:::proof "thm:solution_local"
{uses "thm:local_rational"}[] {uses "lem:radius_noperthedron_one"}[] {uses "lem:congruent"}[]
:::

```tex
\begin{proof}
\uses{thm:local_rational,lem:radius_noperthedron_one,lem:congruent}
\end{proof}
```

:::theorem "thm:row_valid_imp_not_rupert_ix" (lean := "Solution.Row.valid_imp_not_rupert_ix,Solution.valid_split_imp_no_rupert,Solution.valid_binary_split_imp_no_rupert,Solution.valid_full_split_imp_no_rupert,Solution.valid_param_split_imp_no_rupert") (parent := "computational_table_soundness")
{uses "def:noperthedron"}[]

If we have a valid solution table, and in particular its $`i`th row is valid,
then there is no Rupert solution of the interval of its $`i`th row.
:::

```tex
\begin{theorem}
\leanok
\lean{Solution.Row.valid_imp_not_rupert_ix,
Solution.valid_split_imp_no_rupert,
Solution.valid_binary_split_imp_no_rupert,
Solution.valid_full_split_imp_no_rupert,
Solution.valid_param_split_imp_no_rupert
}
\label{thm:row_valid_imp_not_rupert_ix}
\uses{def:noperthedron}
If we have a valid solution table, and in particular its $i$th row is valid,
then there is no Rupert solution of the interval of its $i$th row.
\end{theorem}
```

:::proof "thm:row_valid_imp_not_rupert_ix"
{uses "thm:solution_global"}[] {uses "thm:solution_local"}[]

By a mutual induction on the number of rows left in the table following the $`i`th.
This is because validity constrains each row to only refer to later entries.
Appeal inductively to this same theorem if the row splits into other nodes in
the tree, or appeal to {uses "thm:solution_global"}[Theorem] or {uses "thm:solution_local"}[Theorem] at the leaves.
:::

```tex
\begin{proof}
\leanok
\uses{thm:solution_global, thm:solution_local}
By a mutual induction on the number of rows left in the table following the $i$th. This
is because validity constrains each row to only refer to later entries.
Appeal inductively to this same theorem if the row splits into other nodes in
the tree, or appeal to Theorem~\ref{thm:solution_global} or Theorem~\ref{thm:solution_local}) at the leaves.
\end{proof}
```

:::corollary "thm:row_valid_imp_not_rupert" (lean := "Solution.Row.valid_imp_not_rupert") (parent := "computational_table_soundness")
{uses "def:noperthedron"}[]

If we have a valid solution table, then there is no Rupert solution of the interval of its zeroth row.
:::

```tex
\begin{corollary}
\leanok
\lean{Solution.Row.valid_imp_not_rupert}
\label{thm:row_valid_imp_not_rupert}
\uses{def:noperthedron}
If we have a valid solution table, then there is no Rupert solution of the interval of its zeroth row.
\end{corollary}
```

:::proof "thm:row_valid_imp_not_rupert"
{uses "thm:row_valid_imp_not_rupert_ix"}[]

Immediate special case of {uses "thm:row_valid_imp_not_rupert_ix"}[this theorem].
:::

```tex
\begin{proof}
\leanok
\uses{thm:row_valid_imp_not_rupert_ix}
Immediate special case of \cref{thm:row_valid_imp_not_rupert_ix}.
\end{proof}
```
