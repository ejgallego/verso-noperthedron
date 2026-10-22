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

#doc (Manual) "Cayley coordinates" =>

%%%
tag := "chap:cayley"
%%%

Angles make rotation matrices transcendental functions of the coordinates. Cayley
coordinates make them rational, so that every quantity in the case analysis becomes a
polynomial after clearing positive denominators.

```tex
Angles make rotation matrices transcendental functions of the coordinates. Cayley
coordinates make them rational, so that every quantity in the case analysis becomes a
polynomial after clearing positive denominators.
```

:::definition "def:cayley" (lean := "Cayley.cayleyDenom, Cayley.cayleyNumeratorMatrix, Cayley.cayleyMatrix")
For $`r = (x, y, z) \in \R^3` let $`D(r) = 1 + x^2 + y^2 + z^2` and

$$`
N(r) = \begin{pmatrix}
    1 + x^2 - y^2 - z^2 & 2(xy - z) & 2(xz + y) \\
    2(xy + z) & 1 - x^2 + y^2 - z^2 & 2(yz - x) \\
    2(xz - y) & 2(yz + x) & 1 - x^2 - y^2 + z^2
  \end{pmatrix}.
`

The *Cayley rotation* of $`r` is $`\mathrm{Cay}(r) = N(r) / D(r)`. It is the
rotation by the unit quaternion proportional to $`(1, x, y, z)`.
:::

```tex
\begin{definition}
\label{def:cayley}
\lean{Cayley.cayleyDenom, Cayley.cayleyNumeratorMatrix, Cayley.cayleyMatrix}
\leanok
For $r = (x, y, z) \in \R^3$ let $D(r) = 1 + x^2 + y^2 + z^2$ and
\[
  N(r) = \begin{pmatrix}
    1 + x^2 - y^2 - z^2 & 2(xy - z) & 2(xz + y) \\
    2(xy + z) & 1 - x^2 + y^2 - z^2 & 2(yz - x) \\
    2(xz - y) & 2(yz + x) & 1 - x^2 - y^2 + z^2
  \end{pmatrix}.
\]
The \emph{Cayley rotation} of $r$ is $\mathrm{Cay}(r) = N(r) / D(r)$. It is the
rotation by the unit quaternion proportional to $(1, x, y, z)$.
\end{definition}
```

The numerator $`N(r)` is a polynomial with integer coefficients, defined over any
commutative ring, and the denominator is positive.

```tex
The numerator $N(r)$ is a polynomial with integer coefficients, defined over any
commutative ring, and the denominator is positive.
```

:::lemma_ "lem:cayley_so3" (lean := "Cayley.cayleyMatrix_mem_SO3, Cayley.cayleyDenom_pos") (uses := "def:cayley")
$`D(r) > 0` and $`\mathrm{Cay}(r) \in SO(3)` for every $`r \in \R^3`.
:::

```tex
\begin{lemma}
\label{lem:cayley_so3}
\lean{Cayley.cayleyMatrix_mem_SO3, Cayley.cayleyDenom_pos}
\leanok
\uses{def:cayley}
$D(r) > 0$ and $\mathrm{Cay}(r) \in SO(3)$ for every $r \in \R^3$.
\end{lemma}
```

:::proof "lem:cayley_so3"
Direct computation: $`N(r) N(r)^T = D(r)^2 I` and $`\det N(r) = D(r)^3`.
:::

```tex
\begin{proof}
\leanok
Direct computation: $N(r) N(r)^T = D(r)^2 I$ and $\det N(r) = D(r)^3$.
\end{proof}
```

:::lemma_ "lem:cayley_rodrigues" (lean := "Cayley.cayleyMatrix_apply_sub, Cayley.num_sub_denom") (uses := "def:cayley")
*Rodrigues form.* For every $`S \in \R^3`,

$$`
N(r) S - D(r) S = 2\,\bigl(r \times S + r \times (r \times S)\bigr).
`

Equivalently $`\mathrm{Cay}(r) S - S = \frac{2}{D(r)} \bigl(r \times S + r \times (r \times S)\bigr)`.
:::

```tex
\begin{lemma}[Rodrigues form]
\label{lem:cayley_rodrigues}
\lean{Cayley.cayleyMatrix_apply_sub, Cayley.num_sub_denom}
\leanok
\uses{def:cayley}
For every $S \in \R^3$,
\[
  N(r) S - D(r) S = 2\,\bigl(r \times S + r \times (r \times S)\bigr).
\]
Equivalently $\mathrm{Cay}(r) S - S = \frac{2}{D(r)} \bigl(r \times S + r \times (r \times S)\bigr)$.
\end{lemma}
```

:::proof "lem:cayley_rodrigues"
Expand $`N(r) S = (1 - |r|^2) S + 2 r (r \cdot S) + 2 r \times S` and use
$`r \times (r \times S) = r (r \cdot S) - |r|^2 S`.
:::

```tex
\begin{proof}
\leanok
Expand $N(r) S = (1 - |r|^2) S + 2 r (r \cdot S) + 2 r \times S$ and use
$r \times (r \times S) = r (r \cdot S) - |r|^2 S$.
\end{proof}
```

The Rodrigues form is the source of the blow-up identity
({bpref "lem:blowup_identity"}[]): the difference $`\mathrm{Cay}(r) S - S` is divisible
by $`r`.

```tex
The Rodrigues form is the source of the blow-up identity
(Lemma~\ref{lem:blowup_identity}): the difference $\mathrm{Cay}(r) S - S$ is divisible
by $r$.
```

:::lemma_ "lem:cayley_trace" (lean := "Cayley.trace_cayleyMatrix") (uses := "def:cayley")
$`\tr \mathrm{Cay}(r) = (3 - |r|^2) / (1 + |r|^2)`.
:::

```tex
\begin{lemma}
\label{lem:cayley_trace}
\lean{Cayley.trace_cayleyMatrix}
\leanok
\uses{def:cayley}
$\tr \mathrm{Cay}(r) = (3 - |r|^2) / (1 + |r|^2)$.
\end{lemma}
```

:::proof "lem:cayley_trace"
Direct computation.
:::

```tex
\begin{proof}
\leanok
Direct computation.
\end{proof}
```

:::theorem "thm:cayley_surj" (lean := "Cayley.exists_cayleyMatrix_of_trace_nonneg") (uses := "lem:cayley_so3")
Every $`A \in SO(3)` with $`\tr A \ge 0` is $`\mathrm{Cay}(r)` for some $`r` with
$`|r|^2 \le 3`.
:::

```tex
\begin{theorem}
\label{thm:cayley_surj}
\lean{Cayley.exists_cayleyMatrix_of_trace_nonneg}
\leanok
\uses{lem:cayley_so3}
Every $A \in SO(3)$ with $\tr A \ge 0$ is $\mathrm{Cay}(r)$ for some $r$ with
$|r|^2 \le 3$.
\end{theorem}
```

:::proof "thm:cayley_surj" (uses := "lem:axis_angle")
Write $`A` as a rotation by angle $`\gamma \in (-\pi, \pi]` about a unit axis $`a`
({bpref "lem:axis_angle"}[]). Then $`\tr A = 1 + 2 \cos\gamma \ge 0` gives
$`\cos\gamma \ge -1/2`. Put $`c = \sin\gamma / (1 + \cos\gamma) = \tan(\gamma/2)` and
$`r = c\,a`. Then $`c^2 = (1 - \cos\gamma)/(1 + \cos\gamma) \le 3`, and comparing the
Rodrigues forms of $`A` and of $`\mathrm{Cay}(r)` gives $`A = \mathrm{Cay}(r)`.
:::

```tex
\begin{proof}
\leanok
\uses{lem:axis_angle}
Write $A$ as a rotation by angle $\gamma \in (-\pi, \pi]$ about a unit axis $a$
(Lemma~\ref{lem:axis_angle}). Then $\tr A = 1 + 2 \cos\gamma \ge 0$ gives
$\cos\gamma \ge -1/2$. Put $c = \sin\gamma / (1 + \cos\gamma) = \tan(\gamma/2)$ and
$r = c\,a$. Then $c^2 = (1 - \cos\gamma)/(1 + \cos\gamma) \le 3$, and comparing the
Rodrigues forms of $A$ and of $\mathrm{Cay}(r)$ gives $A = \mathrm{Cay}(r)$.
\end{proof}
```

:::lemma_ "lem:axis_angle" (lean := "Cayley.BalancedSupport.exists_axisAngle, Cayley.BalancedSupport.AxisAngle.matrix_trace_eq")
*Axis-angle form.* Every $`A \in SO(3)` is a rotation by some angle $`\gamma \in (-\pi, \pi]` about some unit
axis $`a`:
$`A v - v = \sin\gamma\; a \times v + (1 - \cos\gamma)\; a \times (a \times v)`.
Its trace is $`1 + 2\cos\gamma`.
:::

```tex
\begin{lemma}[Axis-angle form]
\label{lem:axis_angle}
\lean{Cayley.BalancedSupport.exists_axisAngle, Cayley.BalancedSupport.AxisAngle.matrix_trace_eq}
\leanok
Every $A \in SO(3)$ is a rotation by some angle $\gamma \in (-\pi, \pi]$ about some unit
axis $a$:
$A v - v = \sin\gamma\; a \times v + (1 - \cos\gamma)\; a \times (a \times v)$.
Its trace is $1 + 2\cos\gamma$.
\end{lemma}
```

:::proof "lem:axis_angle"
Every element of $`SO(3)` is orthogonally conjugate to a rotation $`R_z(\gamma)` about the
$`z`-axis; transport the formula for $`R_z(\gamma)` along the conjugating frame.
:::

```tex
\begin{proof}
\leanok
Every element of $SO(3)$ is orthogonally conjugate to a rotation $R_z(\gamma)$ about the
$z$-axis; transport the formula for $R_z(\gamma)$ along the conjugating frame.
\end{proof}
```

# Outer views

:::definition "def:outer_rot" (lean := "Cayley.outerRot") (uses := "def:cayley")
For $`(u, v) \in \R^2` let $`s(u, v) = \mathrm{Cay}(v, -u, 0)`.
:::

```tex
\begin{definition}
\label{def:outer_rot}
\lean{Cayley.outerRot}
\leanok
\uses{def:cayley}
For $(u, v) \in \R^2$ let $s(u, v) = \mathrm{Cay}(v, -u, 0)$.
\end{definition}
```

:::lemma_ "lem:outer_view" (lean := "Cayley.outerRot_row2") (uses := "def:outer_rot")
The third row of $`s(u, v)`, the *view* $`s(u,v)^T e_z`, is the inverse
stereographic image

$$`
\frac{(2u,\ 2v,\ 1 - u^2 - v^2)}{1 + u^2 + v^2}.
`
:::

```tex
\begin{lemma}
\label{lem:outer_view}
\lean{Cayley.outerRot_row2}
\leanok
\uses{def:outer_rot}
The third row of $s(u, v)$, the \emph{view} $s(u,v)^T e_z$, is the inverse
stereographic image
\[
  \frac{(2u,\ 2v,\ 1 - u^2 - v^2)}{1 + u^2 + v^2}.
\]
\end{lemma}
```

:::proof "lem:outer_view"
Direct computation.
:::

```tex
\begin{proof}
\leanok
Direct computation.
\end{proof}
```

:::lemma_ "lem:outer_unique" (lean := "Cayley.eq_Rz_mul_outerRot") (uses := "lem:outer_view")
If $`R \in SO(3)` has the same third row as $`s(u, v)`, then
$`R = R_z(\gamma)\, s(u, v)` for some $`\gamma`.
:::

```tex
\begin{lemma}
\label{lem:outer_unique}
\lean{Cayley.eq_Rz_mul_outerRot}
\leanok
\uses{lem:outer_view}
If $R \in SO(3)$ has the same third row as $s(u, v)$, then
$R = R_z(\gamma)\, s(u, v)$ for some $\gamma$.
\end{lemma}
```

:::proof "lem:outer_unique"
$`R\, s(u,v)^T` fixes $`e_z`, so it is a rotation about the $`z`-axis.
:::

```tex
\begin{proof}
\leanok
$R\, s(u,v)^T$ fixes $e_z$, so it is a rotation about the $z$-axis.
\end{proof}
```
