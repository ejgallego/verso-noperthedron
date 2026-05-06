/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Verso
import VersoManual
import VersoBlueprint
import Authors
import Macros
import Bibliography
import Noperthedron.Local
import Noperthedron.Local.Congruent

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The Local Theorem" =>

:::group "local_linear_algebra"
Linear-algebra lemmas for local geometry.
:::

:::group "local_spanning"
Spanning criteria for projected triples.
:::

:::group "local_distance_sector"
Distance and local-maximality sector estimates.
:::

:::group "local_congruence"
Congruence characterization tools.
:::

:::group "local_main"
Assembly of the local no-Rupert theorem.
:::

:::lemma_ "lem:pythagoras" (lean := "Local.pythagoras") (parent := "local_linear_algebra")
For any $`P \in \mathbb{R}^3` one has
$`\|M(\theta, \phi) P\|^2=\|P\|^2-\langle X(\theta,\varphi),P\rangle^2`.
:::

```tex
\begin{lemma} \label{lem:pythagoras}
  \lean{Local.pythagoras}
  \leanok
    For any $P \in \mathbb{R}^3$ one has
    $\big\|M(\theta, \phi) P\big\|^2=\|P\|^2-\langle X({\theta,\varphi}),P\rangle^2$.
\end{lemma}
```

:::proof "lem:pythagoras"
See polyhedron.without.rupert, Lemma 21.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 21.
\end{proof}
```

:::definition "def:spanp" (lean := "Local.Spanp") (parent := "local_linear_algebra")
Given $`v_1, \dots, v_n \in \R^n` write $`\mathrm{span}^+(v_1,\dots,v_n)` for the set
(simplicial cone) in $`\R^n` defined by

$$`
\mathrm{span}^+(v_1,\dots,v_n) = \Big\{ w \in \R^n \colon \exists \lambda_1,\dots,\lambda_n > 0 \text{ s.t. } w = \sum_{i=1}^n \lambda_i v_i \Big\},
`
$$

which is the natural restriction of $`\mathrm{span}(v_1,\dots,v_n)` to positive weights.
:::

```tex
\begin{definition} \label{def:spanp}
  \lean{Local.Spanp}
  \leanok
      Given $v_1, \dots, v_n \in \R^n$ write $\mathrm{span}^+(v_1,\dots,v_n)$ for the set (simplicial cone) in $\R^n$ defined by
    \[
        \mathrm{span}^+(v_1,\dots,v_n) = \Big\{ w \in \R^n \colon \exists \lambda_1,\dots,\lambda_n > 0 \text{ s.t. } w = \sum_{i=1}^n \lambda_i v_i \Big\},
    \]
    which is the natural restriction of $\mathrm{span}(v_1,\dots,v_n)$ to positive weights.
\end{definition}
```

:::lemma_ "lem:langles" (lean := "Local.langles") (parent := "local_linear_algebra")
Let $`V_1,V_2,V_3,Y,Z \in \mathbb{R}^3` with $`\|Y \|=\| Z \|` and
$`Y,Z \in \mathrm{span}^+(V_1,V_2,V_3)`.
Then at least one of the following inequalities fails:

- $`\langle V_1, Y \rangle > \langle V_1, Z \rangle`
- $`\langle V_2, Y \rangle > \langle V_2, Z \rangle`
- $`\langle V_3, Y \rangle > \langle V_3, Z \rangle`
:::

```tex
\begin{lemma} \label{lem:langles}
  \lean{Local.langles}
  \leanok
Let $V_1,V_2,V_3,Y,Z \in \R^3$ with $\|Y \|=\| Z \|$ and $Y,Z \in \mathrm{span}^+(V_1,V_2,V_3)$. Then at least one of the following inequalities does not hold:
\begin{align*}
    \langle V_1, Y \rangle > \langle V_1, Z \rangle,\\
    \langle V_2, Y \rangle > \langle V_2, Z \rangle,\\
    \langle V_3, Y \rangle > \langle V_3, Z \rangle.
\end{align*}
\end{lemma}
```

:::proof "lem:langles"
See polyhedron.without.rupert, Lemma 23.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 23.
\end{proof}
```

:::lemma_ "lem:scalarprodbars" (lean := "Local.abs_sub_inner_bars_le") (parent := "local_linear_algebra")
For $`A,\overline{A},B,\overline{B}\in \mathbb{R}^{n\times n}` and $`P_1,P_2\in \mathbb{R}^n` it holds that

$$`
|\langle AP_1,BP_2\rangle-\langle \overline{A}P_1,\overline{B}P_2\rangle|
\leq \|P_1\|\,\|P_2\|\,\big( \|A-\overline{A}\|\,\|\overline{B}\| + \|\overline{A}\|\,\|B-\overline{B}\|+\|A-\overline{A}\|\,\|B-\overline{B}\|\big).
`
:::

```tex
\begin{lemma} \label{lem:scalarprodbars}
\lean{Local.abs_sub_inner_bars_le}
\leanok
    For $A,\overline{A},B,\overline{B}\in \R^{n\times n}$ and $P_1,P_2\in \R^n$ it holds that
    \[
        |\langle AP_1,BP_2\rangle-\langle \overline{A}P_1,\overline{B}P_2\rangle|\leq \|P_1\|\cdot \|P_2\|\cdot \Big( \|A-\overline{A}\|\cdot \|\overline{B}\| +  \|\overline{A}\|\cdot \|B-\overline{B}\|+\|A-\overline{A}\|\cdot \|B-\overline{B}\|\Big).
    \]
\end{lemma}
```

:::proof "lem:scalarprodbars"
See polyhedron.without.rupert, Lemma 24.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 24.
\end{proof}
```

:::lemma_ "lem:absscalar" (lean := "Local.abs_sub_inner_le") (parent := "local_linear_algebra")
For $`A,B\in \mathbb{R}^{n\times n}` and $`P_1,P_2\in \mathbb{R}^n` one has

$$`
|\langle AP_1,AP_2\rangle-\langle BP_1,BP_2\rangle|
\leq \|P_1\|\,\|P_2\|\,\|A-B\|\,(\|A\|+\|B\| + \|A-B\|).
`
:::

```tex
\begin{lemma} \label{lem:absscalar}
\lean{Local.abs_sub_inner_le}
\leanok
    For $A,B\in \R^{n\times n}$ and $P_1,P_2\in \R^n$ one has
    $$|\langle AP_1,AP_2\rangle-\langle BP_1,BP_2\rangle|\leq \|P_1\|\cdot \|P_2\|\cdot \|A-B\|\cdot \bigg(\|A\|+\|B\| + \|A-B\|\bigg).$$
\end{lemma}
```

:::proof "lem:absscalar"
See polyhedron.without.rupert, Lemma 25.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 25.
\end{proof}
```

:::lemma_ "lem:origintriangle" (lean := "Local.origin_in_triangle") (parent := "local_linear_algebra")
Let $`A,B,C\in \mathbb{R}^2` be such that
$`\langle R(\pi/2) A,B\rangle`,
$`\langle R(\pi/2) B,C\rangle`,
$`\langle R(\pi/2) C,A\rangle > 0`.
Then the origin lies strictly in triangle $`ABC`.
:::

```tex
\begin{lemma} \label{lem:origintriangle}
\lean{Local.origin_in_triangle}
\leanok
    Let $A,B,C\in \mathbb{R}^2$ be such that $
    \langle R({\pi/2}) A,B\rangle,
    \langle R({\pi/2}) B,C\rangle,
    \langle R({\pi/2}) C,A\rangle >0$. Then the origin lies strictly in the triangle $ABC$.
\end{lemma}
```

:::proof "lem:origintriangle"
See polyhedron.without.rupert, Lemma 26.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 26.
\end{proof}
```

:::definition "def:eps-spanning" (lean := "Local.Triangle.Spanning") (parent := "local_spanning") (owner := "david") (tags := "local, spanning, setup") (effort := "medium") (priority := "high")
Let $`\theta, \varphi \in \mathbb{R}`, $`\varepsilon > 0`, and set $`M := M(\theta, \varphi)`.
Three points $`P_1, P_2, P_3 \in \mathbb{R}^3` with $`\|P_1\|, \|P_2\|, \|P_3\| \leq 1`
are called $`\varepsilon`-spanning for $`(\theta, \varphi)` if:

- $`\langle R(\pi/2) M P_1,M P_{2}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
- $`\langle R(\pi/2) M P_2,M P_{3}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
- $`\langle R(\pi/2) M P_3,M P_{1}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
:::

```tex
\begin{definition}
  \label{def:eps-spanning}
  \lean{Local.Triangle.Spanning}
  \leanok
  Let $\theta, \varphi \in \mathbb{R}$, $\varepsilon > 0$, and set $M := M(\theta, \varphi)$.
  Three points $P_1, P_2, P_3 \in \mathbb{R}^3$ with $\|P_1\|, \|P_2\|, \|P_3\| \leq 1$ are
  called $\varepsilon$-spanning for $(\theta, \varphi)$ if it holds that:
\begin{align*}
    \langle R(\pi/2) M P_1,M P_{2}\rangle > 2 \epsilon(\sqrt{2} + \epsilon),\\
    \langle R(\pi/2) M P_2,M P_{3}\rangle > 2 \epsilon(\sqrt{2} + \epsilon),\\
    \langle R(\pi/2) M P_3,M P_{1}\rangle > 2 \epsilon(\sqrt{2} + \epsilon).
\end{align*}
\end{definition}
```

:::lemma_ "lem:eps-spanning" (lean := "Local.vecX_spanning") (parent := "local_spanning") (owner := "jason") (tags := "local, spanning, proof") (effort := "medium") (priority := "high")
Using {uses "def:eps-spanning"}[] and {uses "def:spanp"}[].

Let $`P_1, P_2, P_3 \in \mathbb{R}^3` with $`\|P_1\|,\|P_2\|,\|P_3\| \leq 1` be
$`\epsilon`-spanning for $`(\bar\theta, \bar\phi)` and let
$`\theta, \phi \in \mathbb{R}` satisfy
$`|\theta - \bar{\theta}|, |\phi - \bar{\phi}| \leq \epsilon`.
If $`\langle X(\theta, \phi), P_i \rangle > 0` for $`i=1,2,3`, then
$`X(\theta, \phi) \in \spanp(P_1, P_2, P_3)`.
:::

```tex
\begin{lemma} \label{lem:eps-spanning}
  \uses{def:eps-spanning, def:spanp}
  \lean{Local.vecX_spanning}
  \leanok
    Let $P_1, P_2, P_3 \in \R^3$ with $\|P_1\|,\|P_2\|,\|P_3\| \leq 1$ be $\epsilon$-spanning for $(\thetab, \phib)$ and let $\theta, \phi \in \R$ such that $|\theta - \overline{\theta}|, |\phi - \overline{\phi}| \leq \epsilon$. Assume that $\langle X(\theta, \phi), P_i \rangle > 0$ for $i=1,2,3$. Then
    \[
        X(\theta, \phi) \in \spanp(P_1, P_2, P_3).
    \]
\end{lemma}
```

:::proof "lem:eps-spanning"
Using {uses "lem:scalarprodbars"}[], {uses "lem:origintriangle"}[], and {uses "lem:sqrt2"}[].
See polyhedron.without.rupert, Lemma 28.
:::

```tex
\begin{proof}
\uses{lem:scalarprodbars, lem:origintriangle, lem:sqrt2}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 28.
\end{proof}
```

:::lemma_ "lem:inCirc" (lean := "Local.inCirc") (parent := "local_distance_sector")
Let $`P, Q \in \mathbb{R}^3` with $`\|P\|, \|Q\| \leq 1`, and let
$`\epsilon>0`, $`\bar\theta_1,\bar\phi_1,\bar\theta_2,\bar\phi_2,\bar\alpha \in \mathbb{R}`.
Set

$$`
T := \left(R(\bar\alpha) M(\bar\theta_1, \bar\phi_1) P + M(\bar\theta_2, \bar\phi_2) Q\right)/2 \in \mathbb{R}^2,
`

and assume $`\delta \geq \|T - M(\bar\theta_2, \bar\phi_2) Q\|`.
If $`|\bar\theta_1-\theta_1|, |\bar\phi_1-\phi_1|, |\bar\theta_2-\theta_2|, |\bar\phi_2-\phi_2|, |\bar\alpha - \alpha| \leq \epsilon`,
then $`R(\alpha)M(\theta_1, \phi_1) P` and $`M(\theta_2, \phi_2) Q` lie in
$`\mathrm{Circ}_{\delta + \sqrt{5} \epsilon}(T)`.
:::

```tex
\begin{lemma} \label{lem:inCirc}
  \lean{Local.inCirc}
  \leanok
    Let $P, Q \in \R^3$ with $\|P\|, \|Q\| \leq 1$. Let $\epsilon>0$ and $\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \R$, then set
    \[
        T \coloneqq \left(R(\alphab) M(\thetab_1, \phib_1) P + M(\thetab_2, \phib_2) Q\right)/2 \in \R^2,
    \]
    and $\delta \geq \|T - M(\thetab_2, \phib_2) Q\|$. Finally, let $\theta_1, \phi_1, \theta_2, \phi_2, \alpha \in \R$ with $|\thetab_1-\theta_1|, |\phib_1 - \phi_1|, |\thetab_2-\theta_2|, |\phib_2-\phi_2|, |\alphab - \alpha| \leq \epsilon$. Then $R(\alpha)M(\theta_1, \phi_1) P, M(\theta_2, \phi_2) Q \in \Circ_{\delta + \sqrt{5} \epsilon}(T)$.
\end{lemma}
```

:::proof "lem:inCirc"
Using {uses "lem:sqrt2"}[] and {uses "lem:sqrt5"}[].
See polyhedron.without.rupert, Lemma 30.
:::

```tex
\begin{proof}
\uses{lem:sqrt2, lem:sqrt5}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 30.
\end{proof}
```

:::definition "def:LMD" (lean := "Local.LocallyMaximallyDistant") (parent := "local_distance_sector")
Let $`\PP \subset \R^2` be a convex polygon and $`Q \in \PP` one of its vertices.
Assume that for some $`\overline{Q} \in \R^2` it holds that
$`Q \in \Circ_{\delta}(\overline{Q})`, i.e. $`\|Q - \overline{Q}\| < \delta`.
Define $`\Sect_\delta(\overline{Q}) \coloneqq \Circ_{\delta}(\overline{Q}) \cap \PP^\circ`
as the intersection between $`\Circ_{\delta}(\overline{Q})` and the interior of the convex hull of $`\PP`.

Moreover, $`Q \in \PP` is called $`\delta`-locally maximally distant with respect to
$`\overline{Q}` ($`\delta`-LMD$`(\overline{Q})`) if for all $`A \in \Sect_\delta(\overline{Q})`
it holds that $`\|Q\| > \|A\|`.
:::

```tex
\begin{definition}
  \label{def:LMD}
  \lean{Local.LocallyMaximallyDistant}
  \leanok
    Let $\PP \subset \R^2$ be a convex polygon and $Q \in \PP$ one of its vertices. Assume that for some $\overline{Q} \in \R^2$ it holds that $Q \in \Circ_{\delta}(\overline{Q})$, i.e. $\|Q - \overline{Q}\| < \delta$. Define $\Sect_\delta(\overline{Q}) \coloneqq \Circ_{\delta}(\overline{Q}) \cap \PP^\circ$ as the intersection between $\Circ_{\delta}(\overline{Q})$ and the interior of the convex hull of $\PP$.

    Moreover, $Q \in \PP$ is called \emph{$\delta$-locally maximally distant with respect to $\overline{Q}$ ($\delta$-LMD$(\overline{Q})$)} if for all $A \in \Sect_\delta(\overline{Q})$ it holds that $\|Q\| > \|A\|$.
\end{definition}
```

:::lemma_ "lem:LMD" (lean := "Local.inner_ge_implies_LMD") (parent := "local_distance_sector")
Using {uses "def:LMD"}[].

Let $`\mathbf{P}` be a convex polygon and $`Q \in \mathbf{P}` a vertex.
Let $`\overline{Q} \in \mathbb{R}^2` with $`\|Q - \overline{Q}\| < \delta` for some $`\delta>0`.
Assume there exists $`r > 0` with $`\|Q\| > r` such that

$$`
\frac{\langle Q, Q - P_j \rangle}{\|Q\|\|Q - P_j\|} \geq \delta/r
`

for all other vertices $`P_j \in \mathbf{P} \setminus Q`.
Then $`Q` is $`\delta`-locally maximally distant with respect to $`\overline{Q}`.
:::

```tex
\begin{lemma} \label{lem:LMD}
  \uses{def:LMD}
  \lean{Local.inner_ge_implies_LMD}
  \leanok
    Let $\PP$ be a convex polygon and $Q \in \PP$ be one of its vertices. Let $\overline{Q} \in \R^2$ with $\|Q - \overline{Q}\| < \delta$ for some $\delta>0$. Assume that for some $r > 0 $ such that $\|Q\| > r$ it holds that
    \[
        \frac{\langle Q, Q - P_j \rangle}{\|Q\|\|Q - P_j\|} \geq \delta/r,
    \]
    for all other vertices $P_j \in \PP \setminus Q$. Then $Q \in \PP$ is $\delta$-locally maximally distant with respect to $\overline{Q}$.
\end{lemma}
```

:::proof "lem:LMD"
See polyhedron.without.rupert, Lemma 32.
:::

```tex
\begin{proof}\leanok
See \cite{polyhedron.without.rupert}, Lemma 32.
\end{proof}
```

:::lemma_ "lem:coss" (lean := "Local.coss") (parent := "local_distance_sector")
Let $`\epsilon>0` and $`\theta,\bar\theta, \phi, \bar\phi \in \mathbb{R}` with
$`|\theta - \bar{\theta}|, |\phi - \bar{\phi}| \leq \epsilon`.
Define $`M = M(\theta, \phi)` and $`\overline{M} = M(\bar\theta, \bar\phi)`,
and let $`P, Q \in \mathbb{R}^3` with $`\|P\|, \|Q\| \leq 1`.
Assume that

$$`
\frac{\langle \overline{M} P,\overline{M} (P-Q)\rangle - 2 \epsilon \|P-Q\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\overline{M} P\|+\sqrt{2} \varepsilon \big) \cdot \big(\|\overline{M}(P-Q)\|+2 \sqrt{2} \varepsilon\big)} > 0.
`
$$

Then:

$$`
\frac{\langle MP,M(P-Q)\rangle}{\|MP\|\,\|M(P-Q)\|}
\geq
\frac{\langle \overline{M} P,\overline{M} (P-Q)\rangle - 2 \epsilon \|P-Q\| \cdot (\sqrt{2}+\varepsilon)}{ (\|\overline{M} P\|+\sqrt{2} \varepsilon ) \cdot (\|\overline{M}(P-Q)\|+2 \sqrt{2} \varepsilon)}.
`
:::

```tex
\begin{lemma} \label{lem:coss}
  \lean{Local.coss}
  \leanok
  Let $\epsilon>0$ and $\theta,\thetab, \phi, \phib \in \R$ with $|\theta - \overline{\theta}|, |\phi - \overline{\phi}| \leq \epsilon$. Define $M = M(\theta, \phi)$ and $\overline{M} = M(\thetab, \phib)$ and let $P, Q \in \R^3$ with $\|P\|, \|Q\| \leq 1$. Assume that
    \[
        \frac{\langle \overline{M} P,\overline{M} (P-Q)\rangle - 2 \epsilon \|P-Q\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\overline{M} P\|+\sqrt{2} \varepsilon \big) \cdot \big(\|\overline{M}(P-Q)\|+2 \sqrt{2} \varepsilon\big)} > 0.
    \]
  Then:
    \[
        \frac{\langle {M} P,{M} (P-Q)\rangle}{\|{M} P\| \cdot \|{M}(P-Q)\|} \geq
        \frac{\langle \overline{M} P,\overline{M} (P-Q)\rangle - 2 \epsilon \|P-Q\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\overline{M} P\|+\sqrt{2} \varepsilon \big) \cdot \big(\|\overline{M}(P-Q)\|+2 \sqrt{2} \varepsilon\big)}.
    \]
\end{lemma}
```

:::proof "lem:coss"
Using {uses "lem:absscalar"}[] and {uses "lem:sqrt2"}[].
See polyhedron.without.rupert, Lemma 33.
:::

```tex
\begin{proof}
\uses{lem:absscalar, lem:sqrt2}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 33.
\end{proof}
```

:::lemma_ "lem:congruent" (lean := "Local.congruent_iff_sym_matrix_eq") (parent := "local_congruence") (owner := "jason") (tags := "local, congruence") (effort := "small") (priority := "medium")
Let $`P_1,P_2,P_3, Q_1,Q_2,Q_3 \in \mathbb{R}^3`.
Define $`P := (P_1|P_2|P_3)` and $`Q := (Q_1|Q_2|Q_3)` and assume $`Q` is invertible.
Then $`P_1, P_2, P_3` and $`Q_1, Q_2, Q_3` are congruent iff $`P^t P = Q^t Q`.
:::

```tex
\begin{lemma} \label{lem:congruent}
\leanok
\lean{Local.congruent_iff_sym_matrix_eq}
    Let $P_1,P_2,P_3, Q_1,Q_2,Q_3 \in \R^3$. Define the $3 \times 3$ matrices $P \coloneqq (P_1|P_2|P_3)$ and $Q \coloneqq (Q_1|Q_2|Q_3)$ and assume that $Q$ is invertible.
    Then $P_1, P_2, P_3$ and $Q_1, Q_2, Q_3$ are congruent if and only if $P^t P = Q^t Q$.
\end{lemma}
```

:::proof "lem:congruent"
From polyhedron.without.rupert, Lemma 35.
Note that $`P^t P = Q^t Q` is equivalent to saying that
$`\langle P_i,P_j\rangle = \langle Q_i,Q_j\rangle` for all $`1 \leq i,j \leq 3`.
Moreover, the condition on invertibility of $`Q` can be dropped, however then
the proof becomes somewhat less straightforward.

If $`P_1, P_2, P_3` and $`Q_1, Q_2, Q_3` are congruent then
$`\langle P_i,P_j\rangle = \langle LQ_i,LQ_j\rangle = \langle Q_i,Q_j\rangle`,
thus $`P^t P = Q^t Q`.
For the other direction, we claim that $`L \coloneqq PQ^{-1}` is orthonormal and
satisfies that $`P_i = LQ_i` for all $`i=1,2,3`.
Indeed,  $`L^t L = (PQ^{-1})^t (PQ^{-1}) = (Q^t)^{-1} P^t P Q^{-1} = \mathrm{Id}` and
it holds that $`LQ=PQ^{-1}Q=P`, thus $`LQ_i = P_i`.
:::

```tex
\begin{proof}
\leanok
From \cite{polyhedron.without.rupert}, Lemma 35.
Note that $P^t P = Q^t Q$ is equivalent to saying that $\langle P_i,P_j\rangle = \langle Q_i,Q_j\rangle$ for all $1 \leq i,j \leq 3$. Moreover, the condition on invertibility of $Q$ can be dropped, however then the proof becomes somewhat less straightforward.

    If $P_1, P_2, P_3$ and $Q_1, Q_2, Q_3$ are congruent then $\langle P_i,P_j\rangle = \langle LQ_i,LQ_j\rangle = \langle Q_i,Q_j\rangle$, thus $P^t P = Q^t Q$.
    For the other direction, we claim that $L \coloneqq PQ^{-1}$ is orthonormal and satisfies that $P_i = LQ_i$ for all $i=1,2,3$.
    Indeed,  $L^t L = (PQ^{-1})^t (PQ^{-1}) = (Q^t)^{-1} P^t P Q^{-1} = \mathrm{Id}$ and it holds that $LQ=PQ^{-1}Q=P$, thus $LQ_i = P_i$.
\end{proof}
```

:::theorem "thm:local" (lean := "Local.local_theorem") (parent := "local_main") (owner := "david") (tags := "local, main-theorem") (effort := "large") (priority := "high")
Let $`\PPP` be a polyhedron with radius $`\rho=1` and
$`P_1, P_2, P_3, Q_1, Q_2, Q_3 \in \PPP` be not necessarily distinct.
Assume that $`P_1, P_2, P_3` and $`Q_1, Q_2, Q_3` are congruent.

Let $`\epsilon>0` and $`\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \R`, then set
$`\Xib \coloneqq X(\thetab_1,\phib_1), \Xiib \coloneqq X(\thetab_2,\phib_2)` as well as
$`\Mib \coloneqq M(\thetab_1,\phib_1), \Miib \coloneqq M(\thetab_2,\phib_2)`.
Assume that there exist $`\sigma_P, \sigma_Q \in \{0,1\}` such that

$$`
(-1)^{\sigma_P} \langle \Xib,P_i\rangle>\sqrt{2}\varepsilon \quad \text{and} \quad
(-1)^{\sigma_Q} \langle \Xiib , Q_i\rangle>\sqrt{2}\varepsilon,
`
$$

for all $`i=1,2,3`.
Moreover, assume that $`P_1,P_2,P_3` are $`\epsilon`-spanning for $`(\thetab_1,\phib_1)` and that
$`Q_1,Q_2,Q_3` are $`\epsilon`-spanning for $`(\thetab_2,\phib_2)`.
Finally, assume that for all $`i = 1,2,3` and any $`Q_j \in \PPP \setminus Q_i` it holds that

$$`
\frac{\langle \Miib Q_i,\Miib (Q_i-Q_j)\rangle - 2 \epsilon \|Q_i-Q_j\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\Miib Q_i\|+\sqrt{2} \varepsilon \big) \cdot \big(\|\Miib(Q_i-Q_j)\|+2 \sqrt{2} \varepsilon\big)} > \frac{\sqrt{5} \epsilon + \delta}{r},
`
$$

for some $`r >0` such that $`\min_{i=1,2,3}\| \Miib Q_i \| > r + \sqrt{2} \epsilon`
and for some $`\delta \in \R` with

$$`
\delta \geq \max_{i=1,2,3}\left\|R(\alphab) \Mib P_i - \Miib Q_i\right\|/2.
`
$$

Then there exists no solution to Rupert's problem
$`R(\alpha) M(\theta_1,\phi_1)\PPP \subset  M(\theta_2,\phi_2)\PPP^\circ` with

$$`
(\theta_1, \phi_1, \theta_2, \phi_2, \alpha) \in
[\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \coloneqq U \subseteq \R^5.
`
:::

```tex
\begin{theorem}[Local Theorem] \label{thm:local}
\leanok
\lean{Local.local_theorem}
    Let $\PPP$ be a polyhedron with radius $\rho=1$ and $P_1, P_2, P_3, Q_1, Q_2, Q_3 \in \PPP$ be not necessarily distinct. Assume that $P_1, P_2, P_3$ and $Q_1, Q_2, Q_3$ are congruent.

    Let $\epsilon>0$ and $\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \R$, then set $\Xib \coloneqq X(\thetab_1,\phib_1), \Xiib \coloneqq X(\thetab_2,\phib_2)$ as well as $\Mib \coloneqq M(\thetab_1,\phib_1), \Miib \coloneqq M(\thetab_2,\phib_2)$.
    Assume that there exist $\sigma_P, \sigma_Q \in \{0,1\}$ such that
    \[
        (-1)^{\sigma_P} \langle \Xib,P_i\rangle>\sqrt{2}\varepsilon \quad \text{and} \quad
        (-1)^{\sigma_Q} \langle \Xiib , Q_i\rangle>\sqrt{2}\varepsilon, \tag{A$_\epsilon$}
    \]
    for all $i=1,2,3$.
    Moreover, assume that $P_1,P_2,P_3$ are $\epsilon$-spanning for $(\thetab_1,\phib_1)$ and that $Q_1,Q_2,Q_3$ are $\epsilon$-spanning for $(\thetab_2,\phib_2)$.
    Finally, assume that for all $i = 1,2,3$ and any $Q_j \in \PPP \setminus Q_i$ it holds~that
    \[
        \frac{\langle \Miib Q_i,\Miib (Q_i-Q_j)\rangle - 2 \epsilon \|Q_i-Q_j\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\Miib Q_i\|+\sqrt{2} \varepsilon \big) \cdot \big(\|\Miib(Q_i-Q_j)\|+2 \sqrt{2} \varepsilon\big)} > \frac{\sqrt{5} \epsilon + \delta}{r}, \tag{B$_\epsilon$}
    \]
    for some $r >0$ such that $\min_{i=1,2,3}\| \Miib Q_i \| > r + \sqrt{2} \epsilon$ and for some $\delta \in \R$ with
    \[
        \delta \geq \max_{i=1,2,3}\left\|R(\alphab) \Mib P_i - \Miib Q_i\right\|/2.
    \]
    Then there exists no solution to Rupert's problem $R(\alpha) M(\theta_1,\phi_1)\PPP \subset  M(\theta_2,\phi_2)\PPP^\circ$ with
    \[
        (\theta_1, \phi_1, \theta_2, \phi_2, \alpha) \in [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \coloneqq U \subseteq \R^5.
    \]
\end{theorem}
```

:::proof "thm:local"
Using {uses "lem:langles"}[], {uses "lem:XPgt0"}[], {uses "lem:eps-spanning"}[],
{uses "lem:MPgtr"}[], {uses "lem:inCirc"}[], {uses "lem:coss"}[], {uses "lem:LMD"}[], and {uses "lem:pythagoras"}[].
See polyhedron.without.rupert, Theorem 36.
:::

```tex
\begin{proof}\leanok
\uses{lem:langles,lem:XPgt0,lem:eps-spanning,lem:MPgtr,lem:inCirc,lem:coss,lem:LMD,lem:pythagoras}
See \cite{polyhedron.without.rupert}, Theorem 36.
\end{proof}
```
