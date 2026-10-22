/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Macros
import Bibliography
import Cayley

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

#doc (Manual) "Irrational data" =>

%%%
tag := "chap:data"
%%%

The vertices of $`\PPP` and the symmetries $`g_k` involve $`\cos(2\pi k/15)` and
$`\sin(2\pi k/15)`. The checker works with dyadic approximations of these numbers; this
chapter bounds the approximation errors. Nothing else in the proof is irrational.

```tex
The vertices of $\PPP$ and the symmetries $g_k$ involve $\cos(2\pi k/15)$ and
$\sin(2\pi k/15)$. The checker works with dyadic approximations of these numbers; this
chapter bounds the approximation errors. Nothing else in the proof is irrational.
```

:::lemma_ "lem:theta1" (lean := "Cayley.θ₁_eq, Cayley.cos_θ₁_bounds, Cayley.sin_θ₁_bounds")
Let $`\theta_1 = 2\pi/15`. Then $`\theta_1 = \pi/3 - \pi/5`, and $`\cos\theta_1` and
$`\sin\theta_1` are known to $`28` decimal places.
:::

```tex
\begin{lemma}
\label{lem:theta1}
\lean{Cayley.θ₁_eq, Cayley.cos_θ₁_bounds, Cayley.sin_θ₁_bounds}
\leanok
Let $\theta_1 = 2\pi/15$. Then $\theta_1 = \pi/3 - \pi/5$, and $\cos\theta_1$ and
$\sin\theta_1$ are known to $28$ decimal places.
\end{lemma}
```

:::proof "lem:theta1"
$`\cos(\pi/5) = (1 + \sqrt5)/4` and $`\sin(\pi/5) = \sqrt{10 - 2\sqrt5}/4`; expand
$`\cos` and $`\sin` of the difference, and bound $`\sqrt3`, $`\sqrt5` by rationals.
:::

```tex
\begin{proof}
\leanok
$\cos(\pi/5) = (1 + \sqrt5)/4$ and $\sin(\pi/5) = \sqrt{10 - 2\sqrt5}/4$; expand
$\cos$ and $\sin$ of the difference, and bound $\sqrt3$, $\sqrt5$ by rationals.
\end{proof}
```

:::lemma_ "lem:sin_wedge" (lean := "Cayley.sin_θ₁_le_wedge") (uses := "lem:theta1")
$`\sin(2\pi/15) \le \frac{57}{128} \cos(2\pi/15)`.
:::

```tex
\begin{lemma}
\label{lem:sin_wedge}
\lean{Cayley.sin_θ₁_le_wedge}
\leanok
\uses{lem:theta1}
$\sin(2\pi/15) \le \frac{57}{128} \cos(2\pi/15)$.
\end{lemma}
```

:::proof "lem:sin_wedge"
From the bounds of {bpref "lem:theta1"}[].
:::

```tex
\begin{proof}
\leanok
From the bounds of Lemma~\ref{lem:theta1}.
\end{proof}
```

:::lemma_ "lem:trig_table" (lean := "Cayley.trig_err, Cayley.cos_tab_err, Cayley.sin_tab_err") (uses := "lem:theta1")
For $`k = 0, \dots, 14`, the checker's tables of $`\cos(2\pi k/15)` and
$`\sin(2\pi k/15)` (dyadic numbers with denominator $`2^{80}`) are within $`2^{-71}` of the
true values.
:::

```tex
\begin{lemma}
\label{lem:trig_table}
\lean{Cayley.trig_err, Cayley.cos_tab_err, Cayley.sin_tab_err}
\leanok
\uses{lem:theta1}
For $k = 0, \dots, 14$, the checker's tables of $\cos(2\pi k/15)$ and
$\sin(2\pi k/15)$ (dyadic numbers with denominator $2^{80}$) are within $2^{-71}$ of the
true values.
\end{lemma}
```

:::proof "lem:trig_table"
Let $`z_k = e^{2\pi i k/15}` and let $`\hat z_k` be the table entry. Then
$`|z_1 - \hat z_1| \le 2^{-79}` by {bpref "lem:theta1"}[], and
$`z_{k+1} = z_k z_1`, so
$`|z_{k+1} - \hat z_{k+1}| \le |z_k - \hat z_k| + |\hat z_k|\, 2^{-79} + |\hat z_k \hat z_1 - \hat z_{k+1}|`.
The last two terms are computed exactly in $`\Q` and are at most $`2^{-75}` for each $`k`,
so $`|z_k - \hat z_k| \le k\, 2^{-75}`.
:::

```tex
\begin{proof}
\leanok
Let $z_k = e^{2\pi i k/15}$ and let $\hat z_k$ be the table entry. Then
$|z_1 - \hat z_1| \le 2^{-79}$ by Lemma~\ref{lem:theta1}, and
$z_{k+1} = z_k z_1$, so
$|z_{k+1} - \hat z_{k+1}| \le |z_k - \hat z_k| + |\hat z_k|\, 2^{-79} + |\hat z_k \hat z_1 - \hat z_{k+1}|$.
The last two terms are computed exactly in $\Q$ and are at most $2^{-75}$ for each $k$,
so $|z_k - \hat z_k| \le k\, 2^{-75}$.
\end{proof}
```

:::lemma_ "lem:vertex_approx" (lean := "Cayley.cTab_err, Cayley.vertex_approx, Cayley.Pack.vR_err") (uses := "lem:trig_table, def:noperthedron")
Every coordinate of every tabulated vertex is within $`2^{-60}` of the corresponding
coordinate of the true vertex of $`\PPP`.
:::

```tex
\begin{lemma}
\label{lem:vertex_approx}
\lean{Cayley.cTab_err, Cayley.vertex_approx, Cayley.Pack.vR_err}
\leanok
\uses{lem:trig_table, def:noperthedron}
Every coordinate of every tabulated vertex is within $2^{-60}$ of the corresponding
coordinate of the true vertex of $\PPP$.
\end{lemma}
```

:::proof "lem:vertex_approx"
The points $`C_1, C_2, C_3` are rational and tabulated within $`2^{-80}`. A vertex is
$`\pm R_z(2\pi k/15) C_i`; the error of a product of approximations is bounded by the sum
of the errors, since all factors are bounded by $`1`.
:::

```tex
\begin{proof}
\leanok
The points $C_1, C_2, C_3$ are rational and tabulated within $2^{-80}$. A vertex is
$\pm R_z(2\pi k/15) C_i$; the error of a product of approximations is bounded by the sum
of the errors, since all factors are bounded by $1$.
\end{proof}
```

:::lemma_ "lem:group_approx" (lean := "Cayley.group_approx") (uses := "lem:trig_table")
Every entry of every tabulated rotation $`\hat g_k` is within $`2^{-60}` of the
corresponding entry of $`g_k = R_z(2\pi k/15)`.
:::

```tex
\begin{lemma}
\label{lem:group_approx}
\lean{Cayley.group_approx}
\leanok
\uses{lem:trig_table}
Every entry of every tabulated rotation $\hat g_k$ is within $2^{-60}$ of the
corresponding entry of $g_k = R_z(2\pi k/15)$.
\end{lemma}
```

:::proof "lem:group_approx"
Immediate from {bpref "lem:trig_table"}[].
:::

```tex
\begin{proof}
\leanok
Immediate from Lemma~\ref{lem:trig_table}.
\end{proof}
```

The pairing used in the blow-up of chart 4 is exact: $`\tau` maps true vertices to true
vertices ({bpref "lem:tau_pair"}[]), and the blow-up bracket $`L` is linear in $`S`, so the
same vertex error bound applies to it.

```tex
The pairing used in the blow-up of chart 4 is exact: $\tau$ maps true vertices to true
vertices (Lemma~\ref{lem:tau_pair}), and the blow-up bracket $L$ is linear in $S$, so the
same vertex error bound applies to it.
```
