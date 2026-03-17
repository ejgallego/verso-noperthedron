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
import Noperthedron.Global

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

tex_prelude r#"
\newcommand{\hull}[1]{\mathsf{Co}(#1)}
"#

#doc (Manual) "The Global Theorem" =>

:::group "global_support_bounds"
Support-function bounds for convex hull projections.
:::

:::group "global_derivative_bounds"
Derivative bounds and approximation control for rotated projections.
:::

:::group "global_main"
Assembly of the global no-Rupert theorem.
:::

:::lemma_ "lem:hullscalarprod" (lean := "GlobalTheorem.hull_scalar_prod") (parent := "global_support_bounds")
Suppose $`V = V_1, \ldots, V_m \subseteq \mathbb{R}^n` is a finite sequence of points,
and let $`\hull V` be its convex hull.
If $`S \in \hull V` and $`w \in \mathbb{R}^n`, then

$$`
\langle S ,w \rangle \leq \max_i \langle V_i ,w\rangle.
`
:::

:::proof "lem:hullscalarprod" (leanok := true)
This is a mild generalization of {citet polyhedron.without.rupert (kind := lemma) (index := 18)}[].
:::

:::lemma_ "lem:leq1" (lean := "GlobalTheorem.rotation_partials_bounded") (parent := "global_derivative_bounds")
Let $`S \in \mathbb{R}^3` and $`w \in \mathbb{R}^2` be unit vectors, and set
$`f(x_1,x_2,x_3) = \langle R(x_3) M(x_1,x_2)S,w \rangle`.
Then for all $`x_1,x_2,x_3 \in \mathbb{R}` and any $`i,j \in \{1,2,3\}` it holds that

$$`
\left|\frac{\partial^2 f}{\partial x_i \partial x_j}(x_1,x_2,x_3)\right|\leq 1.
`
:::

:::proof "lem:leq1" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 19)}[].
:::

:::lemma_ "lem:n2" (lean := "GlobalTheorem.bounded_partials_control_difference") (parent := "global_derivative_bounds")
Let $`f:\mathbb{R}^n\to \mathbb{R}` be a $`C^2`-function and
$`x_1,\dots,x_n,y_1,\dots,y_n \in \mathbb{R}` such that
$`|x_1-y_1|,\dots,|x_n-y_n|\leq \varepsilon`.
If
$`|\partial_{x_i}\partial_{x_j}f(v)| \leq 1`
for all $`i,j \in \{1,\dots,n\}` and all $`v \in \mathbb{R}^n`, then

$$`
|f(x_1,\dots,x_n)-f(y_1,\dots,y_n)|\leq
\varepsilon \sum_{i=1}^n |\partial_{x_i} f(x_1,\dots,x_n)| + \frac{n^2}{2}\varepsilon^2.
`
:::

:::proof "lem:n2" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 20)}[].
:::

:::lemma_ "lem:rotation_derivatives" (lean := "GlobalTheorem.rotation_partials_exist,GlobalTheorem.rotation_partials_exist_outer,GlobalTheorem.partials_helper0,GlobalTheorem.partials_helper1,GlobalTheorem.partials_helper2,GlobalTheorem.partials_helper3,GlobalTheorem.partials_helper4") (parent := "global_derivative_bounds")
The partial derivatives of all relevant rotations, projections, and inner products
used in the Global Theorem are as expected. Specifically:

- $`f^\alpha(\theta,\phi,\alpha) = \langle R'(\alpha) M(\theta, \phi) S, w \rangle`
- $`f^\theta(\theta,\phi,\alpha) = \langle R(\alpha) M^\theta(\theta, \phi) S, w \rangle`
- $`f^\phi(\theta,\phi,\alpha) = \langle R(\alpha) M^\phi(\theta, \phi) S, w \rangle`
- $`g^\theta(\theta,\phi) = \langle  M^\theta(\theta, \phi) P, w \rangle`
- $`g^\phi(\theta,\phi) = \langle  M^\phi(\theta, \phi) P, w \rangle`

where
$`f(\theta,\phi,\alpha) =  \langle R(\alpha) M(\theta,\phi) S / \|S\|, w\rangle`
and
$`g(\theta,\phi) =  \langle M(\theta,\phi) P / \|P\|, w\rangle`.
:::

:::proof "lem:rotation_derivatives" (leanok := true)
By basic properties of derivatives.
:::

:::theorem "thm:global" (lean := "GlobalTheorem.global_theorem") (parent := "global_main")
Let $`\mathbf{P}` be a pointsymmetric convex polyhedron with radius $`\rho = 1`,
let $`S \in \mathbf{P}`, and let
$`\bar\theta_1,\bar\phi_1,\bar\theta_2,\bar\phi_2,\bar\alpha \in \mathbb{R}`.
Let $`w\in\mathbb{R}^2` be a unit vector.
Set
$`\bar M_1 := M(\bar\theta_1,\bar\phi_1)`,
$`\bar M_2 := M(\bar\theta_2,\bar\phi_2)`,
and define $`G` and $`H_P` as in the paper.
If $`G > \max_{P\in\mathbf{P}} H_P`, then there does not exist a Rupert solution with

$$`
(\theta_1,\varphi_1,\theta_2,\varphi_2,\alpha)
\in [\bar\theta_1\pm\epsilon,\bar\phi_1\pm\epsilon,\bar\theta_2\pm\epsilon,\bar\phi_2\pm\epsilon,\bar\alpha\pm\epsilon].
`
:::

:::proof "thm:global" (leanok := true)
Using {uses "lem:hullscalarprod"}[], {uses "lem:leq1"}[], {uses "lem:n2"}[], and {uses "lem:rotation_derivatives"}[].
See {citet polyhedron.without.rupert (kind := section) (index := "4.2")}[].
:::
