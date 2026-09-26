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

:::group "computational_rational_vertices"
Certified rational approximations of the noperthedron vertices.
:::

:::group "computational_table_soundness"
Soundness of table rows and propagated non-Rupert certificates.
:::

:::definition "def:nopertQ" (parent := "computational_rational_vertices")
We define rational approximations of the 90 noperthedron vertices by
$`\lfloor x \cdot 10^{16} \rfloor/10^{16}`.
:::

```tex
\begin{definition}\label{def:nopertQ}\leanok
  We define rational approximations of the 90 noperthedron vertices
  by $\lfloor x \cdot 10^{16} \rfloor/10^{16}$.
\end{definition}
```

:::theorem "thm:nopertQ_approximate" (lean := "Noperthedron.KappaApprox.exact_κApprox_python") (parent := "computational_rational_vertices") (uses := "def:nopertQ")
The rational vertex set $`\mathtt{nopertQ}` is a $`\kappa`-rational approximation
of the Noperthedron.
:::

```tex
\begin{theorem}
  \label{thm:nopertQ_approximate}
  \lean{Noperthedron.KappaApprox.exact_κApprox_python}\leanok
\uses{def:nopertQ}
\tt{nopertQ} is a $\kappa$-rational approximation of the Noperthedron.
\end{theorem}
```

:::proof "thm:nopertQ_approximate"
:::

```tex
\begin{proof}\leanok
\end{proof}
```

:::theorem "thm:exists_solution_table" (parent := "computational_table_construction")
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
\label{thm:exists_solution_table}
\leanok
There exists a valid solution table whose zeroth row covers
\begin{align*}
\theta_1,\theta_2&\in[0,2\pi/15] \subset [0,0.42], \\
\varphi_1&\in [0,\pi] \subset [0,3.15],\\
\varphi_2&\in [0,\pi/2] \subset [0,1.58],\\
\alpha &\in [-\pi/2,\pi/2] \subset [-1.58,1.58].
\end{align*}
\end{theorem}
```

:::proof "thm:exists_solution_table" (uses := "def:nopertQ")
By exhibiting the table and running the validity checking algorithm.
Formalized as $`\mathtt{Noperthedron.NativeCaseAnalysis.solutionTable}` in the
build-on-demand $`\mathtt{NativeCaseAnalysis}` library (checked with
$`\mathtt{native\_decide}`) and independently in the kernel-only
$`\mathtt{KernelCaseAnalysis}` library (checked with $`\mathtt{decide +kernel}`,
using only the standard axioms); both are kept out of the default build targets
so that CI runs stay fast.
:::

```tex
\begin{proof}\leanok
\uses{def:nopertQ}
By exhibiting the table and running the validity checking algorithm.
Formalized as \texttt{Noperthedron.NativeCaseAnalysis.solutionTable}
in the build-on-demand \texttt{NativeCaseAnalysis} library (checked with
\texttt{native\_decide}) and independently in the kernel-only
\texttt{KernelCaseAnalysis} library (checked with \texttt{decide +kernel},
using only the standard axioms); both are kept out of the default build
targets so that CI runs stay fast.
\end{proof}
```

:::theorem "thm:solution_global" (lean := "Noperthedron.Solution.valid_global_imp_no_rupert") (parent := "computational_table_soundness")
If a global node in the solution tree is valid, then there is no Rupert solution for its interval.
:::

```tex
\begin{theorem}
\label{thm:solution_global}
If a global node in the solution tree is valid, then there is no Rupert solution for its interval.
\leanok
\lean{Noperthedron.Solution.valid_global_imp_no_rupert}
\end{theorem}
```

:::proof "thm:solution_global" (uses := "thm:global_rational, thm:nopertQ_approximate")
:::

```tex
\begin{proof}\leanok
\uses{thm:global_rational,thm:nopertQ_approximate}
\end{proof}
```

:::theorem "thm:solution_local" (lean := "Noperthedron.Solution.valid_local_imp_no_rupert") (parent := "computational_table_soundness")
If a local node in the solution tree is valid, then there is no Rupert solution for its interval.
:::

```tex
\begin{theorem}
\label{thm:solution_local}
If a local node in the solution tree is valid, then there is no Rupert solution for its interval.
\leanok
\lean{Noperthedron.Solution.valid_local_imp_no_rupert}
\end{theorem}
```

:::proof "thm:solution_local" (uses := "thm:local_rational, lemma:nopert_verts_norm_le_one, lem:congruent, thm:nopertQ_approximate, c1_c2_c3_norms")
:::

```tex
\begin{proof}\leanok
\uses{thm:local_rational,lemma:nopert_verts_norm_le_one,lem:congruent,thm:nopertQ_approximate,c1_c2_c3_norms}
\end{proof}
```

:::theorem "thm:row_valid_imp_not_rupert_ix" (lean := "Noperthedron.Solution.Row.valid_imp_not_rupert_ix,Noperthedron.Solution.valid_split_imp_no_rupert") (parent := "computational_table_soundness") (uses := "def:noperthedron")

If we have a valid solution table, and in particular its $`i`th row is valid,
then there is no Rupert solution of the interval of its $`i`th row.
:::

```tex
\begin{theorem}
\leanok
\lean{Noperthedron.Solution.Row.valid_imp_not_rupert_ix,
Noperthedron.Solution.valid_split_imp_no_rupert
}
\label{thm:row_valid_imp_not_rupert_ix}
\uses{def:noperthedron}
If we have a valid solution table, and in particular its $i$th row is valid,
then there is no Rupert solution of the interval of its $i$th row.
\end{theorem}
```

:::proof "thm:row_valid_imp_not_rupert_ix" (uses := "thm:solution_global, thm:solution_local")

By strong induction on the number of rows left in the table following the $`i`th.
This is because validity constrains each row to only refer to later entries.
For a split row, every point in its interval belongs to a child interval at a
larger index, so the induction hypothesis excludes a Rupert solution there.
At a leaf, apply {uses "thm:solution_global"}[Theorem] or
{uses "thm:solution_local"}[Theorem].
:::

```tex
\begin{proof}
\leanok
\uses{thm:solution_global, thm:solution_local}
By strong induction on the number of rows left in the table following the $i$th. This
is because validity constrains each row to only refer to later entries.
For a split row, every point in its interval belongs to a child interval at a
larger index, so the induction hypothesis excludes a Rupert solution there.
At a leaf, apply Theorem~\ref{thm:solution_global} or Theorem~\ref{thm:solution_local}.
\end{proof}
```

:::corollary "thm:row_valid_imp_not_rupert" (lean := "Noperthedron.Solution.Row.valid_imp_not_rupert") (parent := "computational_table_soundness") (uses := "def:noperthedron")

If we have a valid solution table, then there is no Rupert solution of the interval of its zeroth row.
:::

```tex
\begin{corollary}
\leanok
\lean{Noperthedron.Solution.Row.valid_imp_not_rupert}
\label{thm:row_valid_imp_not_rupert}
\uses{def:noperthedron}
If we have a valid solution table, then there is no Rupert solution of the interval of its zeroth row.
\end{corollary}
```

:::proof "thm:row_valid_imp_not_rupert" (uses := "thm:row_valid_imp_not_rupert_ix")

Immediate special case of {bpref "thm:row_valid_imp_not_rupert_ix"}[].
:::

```tex
\begin{proof}
\leanok
\uses{thm:row_valid_imp_not_rupert_ix}
Immediate special case of \cref{thm:row_valid_imp_not_rupert_ix}.
\end{proof}
```
