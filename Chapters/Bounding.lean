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
import Noperthedron.Bounding

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal
open scoped RealInnerProductSpace

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

set_option verso.code.warnLineLength 0

#doc (Manual) "Bounding Rotations" =>

:::group "bounding_rotation_norms"
Rotation and norm control inequalities.
:::

:::group "bounding_trig_ineq"
Trigonometric inequality reductions.
:::

:::group "bounding_perturbation"
Perturbation bounds for projected points.
:::

:::lemma_ "lem:RaRalpha" (lean := "Bounding.Rx_norm_one,Bounding.Ry_norm_one,Bounding.Rz_norm_one,Bounding.rotR_norm_one,Bounding.rotM_norm_one,Bounding.rotR'_norm_one,Bounding.rotMθ_norm_le_one,Bounding.rotMφ_norm_le_one") (parent := "bounding_rotation_norms")
For any $`\alpha, \theta,\varphi \in \mathbb{R}` and $`a \in \{x,y,z\}` one has
$`\| R(\alpha)\| = \| R_a(\alpha)\| =\| M(\theta, \phi)\| = 1`.
:::

```tex
\begin{lemma} \label{lem:RaRalpha}
\lean{Bounding.Rx_norm_one,Bounding.Ry_norm_one,Bounding.Rz_norm_one,Bounding.rotR_norm_one,Bounding.rotM_norm_one,Bounding.rotR'_norm_one,Bounding.rotMθ_norm_le_one,Bounding.rotMφ_norm_le_one}
\leanok
For any $\alpha, \theta,\varphi \in \R$ and $a \in \{x,y,z\}$ one has $\| R(\alpha)\| = \| R_a(\alpha)\| = \| R'(\alpha) \| =\| M(\theta, \phi)\| = 1$ and $\| M^\theta(\theta,\varphi)\|, \| M^\phi(\theta,\varphi)\| \leq 1$.
\end{lemma}
```

:::proof "lem:RaRalpha"
See polyhedron.without.rupert, Lemma 9.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 9.
\end{proof}
```

```lean "code:lem:RaRalpha"
theorem bp_Rx_norm_one (α : ℝ) : ‖RxL α‖ = 1 := by
  simpa using Bounding.Rx_norm_one α

theorem bp_Ry_norm_one (α : ℝ) : ‖RyL α‖ = 1 := by
  simpa using Bounding.Ry_norm_one α

theorem bp_Rz_norm_one (α : ℝ) : ‖RzL α‖ = 1 := by
  simpa using Bounding.Rz_norm_one α

theorem bp_rotR_norm_one (α : ℝ) : ‖rotR α‖ = 1 := by
  simpa using Bounding.rotR_norm_one α

theorem bp_rotM_norm_one (θ φ : ℝ) : ‖rotM θ φ‖ = 1 := by
  simpa using Bounding.rotM_norm_one θ φ
```

:::lemma_ "lem:RaRa" (lean := "Bounding.norm_rotR_sub_rotR_lt,Bounding.norm_RxL_sub_RxL_eq,Bounding.norm_RyL_sub_RyL_eq,Bounding.norm_RzL_sub_RzL_eq") (parent := "bounding_rotation_norms")
Let $`\epsilon>0`, $`|\alpha-\alphab|\leq\varepsilon` and $`a \in \{x,y,z\}` then
$`\|R_a(\alpha)-R_a({\alphab})\|=\|R(\alpha)-R(\alphab)\| < \varepsilon`.
:::

```tex
\begin{lemma} \label{lem:RaRa}
  \lean{Bounding.norm_rotR_sub_rotR_lt, Bounding.norm_RxL_sub_RxL_eq, Bounding.norm_RyL_sub_RyL_eq, Bounding.norm_RzL_sub_RzL_eq}
  \leanok
Let $\epsilon>0$, $|\alpha-\alphab|\leq\varepsilon$ and $a \in \{x,y,z\}$ then
$\|R_a(\alpha)-R_a({\alphab})\|=\|R(\alpha)-R(\alphab)\| < \varepsilon$.
\end{lemma}
```

:::proof "lem:RaRa"
See polyhedron.without.rupert, Lemma 10.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 10.
\end{proof}
```

```lean "code:lem:RaRa"
theorem bp_norm_rotR_sub_rotR_lt {ε α α_ : ℝ} (hε : 0 < ε) (hα : |α - α_| ≤ ε) :
    ‖rotR α - rotR α_‖ < ε := by
  simpa using Bounding.norm_rotR_sub_rotR_lt hε hα

theorem bp_norm_RxL_sub_RxL_eq {α α_ : ℝ} :
    ‖RxL α - RxL α_‖ = ‖rotR α - rotR α_‖ := by
  simpa using Bounding.norm_RxL_sub_RxL_eq (α := α) (α_ := α_)

theorem bp_norm_RyL_sub_RyL_eq {α α_ : ℝ} :
    ‖RyL α - RyL α_‖ = ‖rotR α - rotR α_‖ := by
  simpa using Bounding.norm_RyL_sub_RyL_eq (α := α) (α_ := α_)

theorem bp_norm_RzL_sub_RzL_eq {α α_ : ℝ} :
    ‖RzL α - RzL α_‖ = ‖rotR α - rotR α_‖ := by
  simpa using Bounding.norm_RzL_sub_RzL_eq (α := α) (α_ := α_)
```

:::lemma_ "lem:jensen" (lean := "Bounding.one_plus_cos_mul_one_plus_cos_ge") (parent := "bounding_trig_ineq")
For all $`a,b \in \mathbb{R}` with $`|a|,|b|\leq 2` the following inequality holds:
$`(1+\cos(a))(1+\cos(b))\geq 2+2\cos\Big(\sqrt{a^2+b^2}\Big)`,
with equality only for $`a=0` or $`b=0`.
:::

```tex
\begin{lemma} \label{lem:jensen}
\lean{Bounding.one_plus_cos_mul_one_plus_cos_ge}
\leanok
    For all $a,b \in \R$ with $|a|,|b|\leq 2$ the following inequality holds:
    \[
        (1+\cos(a))(1+\cos(b))\geq 2+2\cos\Big(\sqrt{a^2+b^2}\Big),
    \]
    with equality only for $a=0$ or $b=0$.
\end{lemma}
```

:::proof "lem:jensen"
Use the Jensen inequality. See polyhedron.without.rupert, Lemma 11.
:::

```tex
\begin{proof}
\leanok
Use the Jensen inequality. See \cite{polyhedron.without.rupert}, Lemma 11.
\end{proof}
```

```lean "code:lem:jensen"
theorem bp_one_plus_cos_mul_one_plus_cos_ge {a b : ℝ} (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    2 + 2 * Real.cos √(a ^ 2 + b ^ 2) ≤ (1 + Real.cos a) * (1 + Real.cos b) := by
  simpa using Bounding.one_plus_cos_mul_one_plus_cos_ge ha hb
```

:::lemma_ "lem:RxRy_wlog" (lean := "Bounding.norm_RxRy_minus_id_le_wlog") (parent := "bounding_trig_ineq")
For any $`|\alpha|,|\beta| \le 2` and any distinct coordinate axes
$`d_1, d_2 \in \{x,y,z\}` one has
$`\|R_{d_1}(\alpha)R_{d_2}(\beta)-\mathrm{id}\| \leq \sqrt{\alpha^2+\beta^2}`
with equality only for $`\alpha = \beta = 0`.
:::

```tex
\begin{lemma} \label{lem:RxRy_wlog}
\lean{Bounding.norm_RxRy_minus_id_le_wlog}
\leanok
For any $|\alpha|,|\beta| \le 2$ and any distinct coordinate
axes $d, d' \in \{x,y,z\}$ one has
\[
    \|R_d(\alpha)R_{d'}(\beta)-\id\| \leq  \sqrt{\alpha^2+\beta^2}
\]
with equality only for $\alpha = \beta = 0$.
\end{lemma}
```

:::proof "lem:RxRy_wlog"
Using {uses "lem:jensen"}[] and {uses "lem:RaRa"}[].
See polyhedron.without.rupert, Lemma 12.
:::

```tex
\begin{proof}
\uses{lem:jensen, lem:RaRa}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 12.
\end{proof}
```

```lean "code:lem:RxRy_wlog"
theorem bp_norm_RxRy_minus_id_le_wlog {d d' : Fin 3} {α β : ℝ} (hd : d ≠ d') (hα : |α| ≤ 2) (hβ : |β| ≤ 2) :
    ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  simpa using Bounding.norm_RxRy_minus_id_le_wlog hd hα hβ
```

:::lemma_ "lem:RxRy" (lean := "Bounding.lemma12,Bounding.lemma12_equality_iff") (parent := "bounding_trig_ineq")
For any $`\alpha,\beta\in \mathbb{R}` one has
$`\|R_x(\alpha)R_y(\beta)-\mathrm{id}\| \leq \sqrt{\alpha^2+\beta^2}`
with equality only for $`\alpha = \beta = 0`.
:::

```tex
\begin{lemma} \label{lem:RxRy}
\lean{Bounding.lemma12, Bounding.lemma12_equality_iff}
\leanok
For any $\alpha,\beta\in \mathbb{R}$ one has
\[
    \|R_x(\alpha)R_y(\beta)-\id\| \leq  \sqrt{\alpha^2+\beta^2}
\]
with equality only for $\alpha = \beta = 0$.
\end{lemma}
```

:::proof "lem:RxRy"
Using {uses "lem:RxRy_wlog"}[].
See polyhedron.without.rupert, Lemma 12.
:::

```tex
\begin{proof}
\leanok
\uses{lem:RxRy_wlog}
See \cite{polyhedron.without.rupert}, Lemma 12.
\end{proof}
```

```lean "code:lem:RxRy"
theorem bp_lemma12 {d d' : Fin 3} {α β : ℝ} (hd : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α ^ 2 + β ^ 2) := by
  simpa using Bounding.lemma12 (d := d) (d' := d') (α := α) (β := β) hd

theorem bp_lemma12_equality_iff {d d' : Fin 3} {α β : ℝ} (hd : d ≠ d') :
    ‖rot3 d α ∘L rot3 d' β - 1‖ = √(α ^ 2 + β ^ 2) ↔ (α = 0 ∧ β = 0) := by
  simpa using Bounding.lemma12_equality_iff (d := d) (d' := d') (α := α) (β := β) hd
```

:::lemma_ "lem:sqrt2" (lean := "Bounding.norm_M_sub_lt,Bounding.norm_X_sub_lt") (parent := "bounding_perturbation")
Let $`\epsilon>0` and $`|\theta-\thetab|,|\varphi-\phib| \leq \varepsilon` then
$`\|M(\theta, \phi)-M(\thetab,\phib)\|, \|X(\theta, \varphi)-X(\thetab,\phib)\| < \sqrt{2}\varepsilon`.
:::

```tex
\begin{lemma} \label{lem:sqrt2}
\lean{Bounding.norm_M_sub_lt, Bounding.norm_X_sub_lt}
\leanok
Let $\epsilon>0$ and $|\theta-\thetab|,|\varphi-\phib| \leq \varepsilon$ then
$\|M(\theta, \phi)-M(\thetab,\phib)\|, \|X({\theta, \varphi})-X(\thetab,\phib)\| < \sqrt{2}\varepsilon.$
\end{lemma}
```

:::proof "lem:sqrt2"
Using {uses "lem:RxRy"}[].
See polyhedron.without.rupert, Lemma 13.
:::

```tex
\begin{proof}
\uses{lem:RxRy}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 13.
\end{proof}
```

```lean "code:lem:sqrt2"
theorem bp_RyL_neg_compose_RyL (α : ℝ) : RyL (-α) ∘L RyL α = ContinuousLinearMap.id _ _ := by
  simpa using Bounding.RyL_neg_compose_RyL (α := α)

theorem bp_RzL_neg_compose_RzL (α : ℝ) : RzL (-α) ∘L RzL α = ContinuousLinearMap.id _ _ := by
  simpa using Bounding.RzL_neg_compose_RzL (α := α)

theorem bp_norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  simpa using Bounding.norm_M_sub_lt hε hθ hφ

theorem bp_norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  simpa using Bounding.norm_X_sub_lt hε hθ hφ
```

:::lemma_ "lem:XPgt0" (lean := "Bounding.XPgt0") (parent := "bounding_perturbation")
Let $`P \in \mathbb{R}^3` with $`\|P\| \leq 1`. Further, let $`\epsilon>0` and
$`\thetab,\phib, \theta, \phi \in \mathbb{R}` such that
$`|\thetab-\theta|, |\phib - \phi| \leq \epsilon`.
If
$`\langle X(\thetab,\phib),P \rangle>\sqrt{2}\varepsilon`
then
$`\langle X(\theta, \phi),P \rangle>0`.
:::

```tex
\begin{lemma} \label{lem:XPgt0}
  \lean{Bounding.XPgt0}
  \leanok
    Let $P \in \R^3$ with $\|P\| \leq 1$. Further, let $\epsilon>0$ and $\thetab,\phib, \theta, \phi \in \R$ such that $|\thetab-\theta|, |\phib - \phi| \leq \epsilon$. If
    \(
        \langle X(\thetab,\phib),P \rangle>\sqrt{2}\varepsilon
    \)
    then
    \(
        \langle X(\theta, \phi),P \rangle>0.
    \)
\end{lemma}
```

:::proof "lem:XPgt0"
Using {uses "lem:sqrt2"}[].
See polyhedron.without.rupert, Lemma 14.
:::

```tex
\begin{proof}
\uses{lem:sqrt2}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 14.
\end{proof}
```

```lean "code:lem:XPgt0"
theorem bp_XPgt0 {P : ℝ³} {ε θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1) (hε : 0 < ε)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hX : √2 * ε < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  simpa using Bounding.XPgt0 hP hε hθ hφ hX
```

:::lemma_ "lem:MPgtr" (lean := "Bounding.norm_M_apply_gt") (parent := "bounding_perturbation")
Let $`P \in \mathbb{R}^3` with $`\|P\| \leq 1`. Further, let $`\epsilon, r>0` and
$`\thetab,\phib, \theta, \phi \in \mathbb{R}` such that
$`|\thetab-\theta|, |\phib - \phi| \leq \epsilon`.
If
$`\| M(\thetab,\phib) P \| > r + \sqrt{2}\varepsilon`
then
$`\| M(\theta,\phi) P \| > r`.
:::

```tex
\begin{lemma} \label{lem:MPgtr}
\lean{Bounding.norm_M_apply_gt}
\leanok
    Let $P \in \R^3$ with $\|P\| \leq 1$. Further, let $\epsilon, r>0$ and $\thetab,\phib, \theta, \phi \in \R$ such that $|\thetab-\theta|, |\phib - \phi| \leq \epsilon$. If
    \(
        \| M(\thetab,\phib) P \| > r + \sqrt{2}\varepsilon
    \)
    then
    \(
        \| M(\theta,\phi) P \| > r.
    \)
\end{lemma}
```

:::proof "lem:MPgtr"
Using {uses "lem:sqrt2"}[].
See polyhedron.without.rupert, Lemma 15.
Corrigendum: the triangle inquality only implies greater than *or equal to*.
:::

```tex
\begin{proof}
\uses{lem:sqrt2}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 15.
Corrigendum: the triangle inquality only implies greater than *or equal to*.
\end{proof}
```

```lean "code:lem:MPgtr"
theorem bp_norm_M_apply_gt {ε r θ θ_ φ φ_ : ℝ} {P : ℝ³} (hP : ‖P‖ ≤ 1) (hε : 0 < ε)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hM : r + √2 * ε < ‖rotM θ_ φ_ P‖) :
    r < ‖rotM θ φ P‖ := by
  simpa using Bounding.norm_M_apply_gt hP hε hθ hφ hM
```

:::lemma_ "lem:sqrt5" (lean := "Bounding.norm_RM_sub_RM_le") (parent := "bounding_perturbation")
Let $`\epsilon>0` and
$`|\theta-\thetab|,|\varphi-\phib|,|\alpha-\alphab|\leq\varepsilon` then
$`\|R(\alpha) M(\theta, \phi)-R(\alphab)M(\thetab,\phib)\| < \sqrt{5} \varepsilon`.
:::

```tex
\begin{lemma} \label{lem:sqrt5}
  \lean{Bounding.norm_RM_sub_RM_le}
  \leanok
    Let $\epsilon>0$ and $|\theta-\thetab|,|\varphi-\phib|,|\alpha-\alphab|\leq\varepsilon$ then
    $\|R(\alpha) M(\theta, \phi)-R(\alphab)M(\thetab,\phib)\| < \sqrt{5} \varepsilon.$
\end{lemma}
```

:::proof "lem:sqrt5"
Using {uses "lem:sqrt2"}[] and {uses "lem:RxRy"}[].
See polyhedron.without.rupert, Lemma 16.
:::

```tex
\begin{proof}
\uses{lem:sqrt2, lem:RxRy}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 16.
\end{proof}
```

```lean "code:lem:sqrt5"
theorem bp_RyL_neg_compose_RyL' (α : ℝ) : RyL (-α) ∘L RyL α = ContinuousLinearMap.id _ _ := by
  simpa using Bounding.RyL_neg_compose_RyL (α := α)

theorem bp_RzL_neg_compose_RzL' (α : ℝ) : RzL (-α) ∘L RzL α = ContinuousLinearMap.id _ _ := by
  simpa using Bounding.RzL_neg_compose_RzL (α := α)

theorem bp_norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  simpa using Bounding.norm_RM_sub_RM_le hε hθ hφ hα
```
