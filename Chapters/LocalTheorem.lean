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

:::proof "lem:pythagoras" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 21)}[].
:::

:::definition "def:spanp" (lean := "Local.Spanp") (parent := "local_linear_algebra")
Given $`v_1, \dots, v_n \in \mathbb{R}^n`, define
$`\mathrm{span}^+(v_1,\dots,v_n)` to be the simplicial cone

$$`
\left\{ w \in \mathbb{R}^n \mid \exists \lambda_1,\dots,\lambda_n > 0,
\; w = \sum_{i=1}^n \lambda_i v_i \right\}.
`
:::

:::lemma_ "lem:langles" (lean := "Local.langles") (parent := "local_linear_algebra")
Let $`V_1,V_2,V_3,Y,Z \in \mathbb{R}^3` with $`\|Y \|=\| Z \|` and
$`Y,Z \in \mathrm{span}^+(V_1,V_2,V_3)`.
Then at least one of the following inequalities fails:

- $`\langle V_1, Y \rangle > \langle V_1, Z \rangle`
- $`\langle V_2, Y \rangle > \langle V_2, Z \rangle`
- $`\langle V_3, Y \rangle > \langle V_3, Z \rangle`
:::

:::proof "lem:langles" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 23)}[].
:::

:::lemma_ "lem:scalarprodbars" (lean := "Local.abs_sub_inner_bars_le") (parent := "local_linear_algebra")
For $`A,\overline{A},B,\overline{B}\in \mathbb{R}^{n\times n}` and $`P_1,P_2\in \mathbb{R}^n` it holds that

$$`
|\langle AP_1,BP_2\rangle-\langle \overline{A}P_1,\overline{B}P_2\rangle|
\leq \|P_1\|\,\|P_2\|\,\big( \|A-\overline{A}\|\,\|\overline{B}\| + \|\overline{A}\|\,\|B-\overline{B}\|+\|A-\overline{A}\|\,\|B-\overline{B}\|\big).
`
:::

:::proof "lem:scalarprodbars" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 24)}[].
:::

:::lemma_ "lem:absscalar" (lean := "Local.abs_sub_inner_le") (parent := "local_linear_algebra")
For $`A,B\in \mathbb{R}^{n\times n}` and $`P_1,P_2\in \mathbb{R}^n` one has

$$`
|\langle AP_1,AP_2\rangle-\langle BP_1,BP_2\rangle|
\leq \|P_1\|\,\|P_2\|\,\|A-B\|\,(\|A\|+\|B\| + \|A-B\|).
`
:::

:::proof "lem:absscalar" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 25)}[].
:::

:::lemma_ "lem:origintriangle" (lean := "Local.origin_in_triangle") (parent := "local_linear_algebra")
Let $`A,B,C\in \mathbb{R}^2` be such that
$`\langle R(\pi/2) A,B\rangle`,
$`\langle R(\pi/2) B,C\rangle`,
$`\langle R(\pi/2) C,A\rangle > 0`.
Then the origin lies strictly in triangle $`ABC`.
:::

:::proof "lem:origintriangle" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 26)}[].
:::

:::definition "def:eps-spanning" (parent := "local_spanning") (owner := "david") (tags := "local, spanning, setup") (effort := "medium") (priority := "high")
Let $`\theta, \varphi \in \mathbb{R}`, $`\varepsilon > 0`, and set $`M := M(\theta, \varphi)`.
Three points $`P_1, P_2, P_3 \in \mathbb{R}^3` with $`\|P_1\|, \|P_2\|, \|P_3\| \leq 1`
are called $`\varepsilon`-spanning for $`(\theta, \varphi)` if:

- $`\langle R(\pi/2) M P_1,M P_{2}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
- $`\langle R(\pi/2) M P_2,M P_{3}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
- $`\langle R(\pi/2) M P_3,M P_{1}\rangle > 2 \epsilon(\sqrt{2} + \varepsilon)`
:::

:::lemma_ "lem:eps-spanning" (lean := "Local.vecX_spanning") (parent := "local_spanning") (owner := "jason") (tags := "local, spanning, proof") (effort := "medium") (priority := "high")
Using {uses "def:eps-spanning"}[] and {uses "def:spanp"}[].

Let $`P_1, P_2, P_3 \in \mathbb{R}^3` with $`\|P_1\|,\|P_2\|,\|P_3\| \leq 1` be
$`\epsilon`-spanning for $`(\bar\theta, \bar\phi)` and let
$`\theta, \phi \in \mathbb{R}` satisfy
$`|\theta - \bar{\theta}|, |\phi - \bar{\phi}| \leq \epsilon`.
If $`\langle X(\theta, \phi), P_i \rangle > 0` for $`i=1,2,3`, then
$`X(\theta, \phi) \in \spanp(P_1, P_2, P_3)`.
:::

:::proof "lem:eps-spanning" (leanok := true)
Using {uses "lem:scalarprodbars"}[], {uses "lem:origintriangle"}[], and {uses "lem:sqrt2"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 28)}[].
:::

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

:::proof "lem:inCirc" (leanok := true)
Using {uses "lem:sqrt2"}[] and {uses "lem:sqrt5"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 30)}[].
:::

:::definition "def:LMD" (lean := "Local.LocallyMaximallyDistant") (parent := "local_distance_sector")
Let $`\mathbf{P} \subset \mathbb{R}^2` be a convex polygon and $`Q \in \mathbf{P}` a vertex.
Assume $`Q \in \mathrm{Circ}_{\delta}(\overline{Q})` for some $`\overline{Q} \in \mathbb{R}^2`.
Define
$`\mathrm{Sect}_\delta(\overline{Q}) := \mathrm{Circ}_{\delta}(\overline{Q}) \cap \mathbf{P}^\circ`.
Then $`Q` is called $`\delta`-locally maximally distant (with respect to $`\overline{Q}`)
if for all $`A \in \mathrm{Sect}_\delta(\overline{Q})` one has $`\|Q\| > \|A\|`.
:::

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

:::proof "lem:LMD" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 32)}[].
:::

:::lemma_ "lem:coss" (lean := "Local.coss") (parent := "local_distance_sector")
Let $`\epsilon>0` and $`\theta,\bar\theta, \phi, \bar\phi \in \mathbb{R}` with
$`|\theta - \bar{\theta}|, |\phi - \bar{\phi}| \leq \epsilon`.
Define $`M = M(\theta, \phi)` and $`\overline{M} = M(\bar\theta, \bar\phi)`,
and let $`P, Q \in \mathbb{R}^3` with $`\|P\|, \|Q\| \leq 1`.
If the rational expression from Lemma 33 is positive, then

$$`
\frac{\langle MP,M(P-Q)\rangle}{\|MP\|\,\|M(P-Q)\|}
\geq
\frac{\langle \overline{M} P,\overline{M} (P-Q)\rangle - 2 \epsilon \|P-Q\| \cdot (\sqrt{2}+\varepsilon)}{ (\|\overline{M} P\|+\sqrt{2} \varepsilon ) \cdot (\|\overline{M}(P-Q)\|+2 \sqrt{2} \varepsilon)}.
`
:::

:::proof "lem:coss" (leanok := true)
Using {uses "lem:absscalar"}[] and {uses "lem:sqrt2"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 33)}[].
:::

:::lemma_ "lem:congruent" (lean := "Local.congruent_iff_sym_matrix_eq") (parent := "local_congruence") (owner := "jason") (tags := "local, congruence") (effort := "small") (priority := "medium")
Let $`P_1,P_2,P_3, Q_1,Q_2,Q_3 \in \mathbb{R}^3`.
Define $`P := (P_1|P_2|P_3)` and $`Q := (Q_1|Q_2|Q_3)` and assume $`Q` is invertible.
Then $`P_1, P_2, P_3` and $`Q_1, Q_2, Q_3` are congruent iff $`P^t P = Q^t Q`.
:::

:::proof "lem:congruent" (leanok := true)
From {citet polyhedron.without.rupert (kind := lemma) (index := 35)}[].
:::

:::theorem "thm:local" (lean := "Local.local_theorem") (parent := "local_main") (owner := "david") (tags := "local, main-theorem") (effort := "large") (priority := "high")
Let $`\mathbf{P}` be a polyhedron of radius $`\rho=1`.
Assume triangles $`P_1,P_2,P_3` and $`Q_1,Q_2,Q_3` in $`\mathbf{P}` are congruent,
assume the sign conditions $`(A_\epsilon)`, the spanning hypotheses, and the quantitative
bound $`(B_\epsilon)` from the paper. Then there is no Rupert solution in the interval

$$`
(\theta_1, \phi_1, \theta_2, \phi_2, \alpha) \in
[\bar\theta_1\pm\epsilon,\bar\phi_1\pm\epsilon,\bar\theta_2\pm\epsilon,\bar\phi_2\pm\epsilon,\bar\alpha\pm\epsilon].
`
:::

:::proof "thm:local" (leanok := true)
Using {uses "lem:langles"}[], {uses "lem:XPgt0"}[], {uses "lem:eps-spanning"}[],
{uses "lem:MPgtr"}[], {uses "lem:inCirc"}[], {uses "lem:coss"}[], {uses "lem:LMD"}[], and {uses "lem:pythagoras"}[].
See {citet polyhedron.without.rupert (kind := theorem) (index := 36)}[].
:::
