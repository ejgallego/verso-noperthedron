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
import Noperthedron.RationalApprox
import Noperthedron.Local

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Rational Versions" =>

:::group "rational_trig_approx"
Rational trigonometric approximations.
:::

:::group "rational_matrix_error"
Matrix approximation error bounds.
:::

:::group "rational_global_transfer"
Transfer of the global theorem to rational approximations.
:::

:::group "rational_local_approx"
Local theorem approximation bounds.
:::

:::group "rational_local_transfer"
Transfer of the local theorem to rational approximations.
:::

:::definition "dfn:sin_cos_approx" (lean := "RationalApprox.sinℚ,RationalApprox.cosℚ") (parent := "rational_trig_approx")
Define $`\ssin, \scos : \mathbb{R} \to \mathbb{R}` by truncated Taylor series:

- $`\ssin(x) := x-\frac{x^3}{3!}+\frac{x^5}{5!}\mp\dots+\frac{x^{25}}{25!}`
- $`\scos(x) := 1-\frac{x^2}{2!}+\frac{x^4}{4!}\mp\dots+\frac{x^{24}}{24!}`

Replacing $`\sin,\cos` with $`\ssin,\scos` defines
$`R_\mathbb{Q}(\alpha), R'_\mathbb{Q}(\alpha), X_\mathbb{Q}(\theta,\phi), M_\mathbb{Q}(\theta,\phi), M^\theta_\mathbb{Q}(\theta,\varphi), M^\phi_\mathbb{Q}(\theta,\varphi)`.
:::

:::lemma_ "lem:sin27cos26" (lean := "RationalApprox.sinℚ_approx,RationalApprox.cosℚ_approx") (parent := "rational_trig_approx")
Using {uses "dfn:sin_cos_approx"}[].

$$`
|\ssin(x)-\sin(x)|\leq \frac{|x|^{27}}{27!}
\qquad\text{and}\qquad
|\scos(x)-\cos(x)|\leq \frac{|x|^{26}}{26!}.
`
:::

:::proof "lem:sin27cos26" (leanok := true)
Use Taylor-series remainder bounds and that all higher derivatives of sine/cosine have absolute value at most 1.
:::

:::lemma_ "lem:kappa7" (lean := "RationalApprox.sinℚ_approx',RationalApprox.cosℚ_approx'") (parent := "rational_trig_approx")
For every $`x\in [-4,4]`,
$`|\ssin(x)-\sin(x)| \leq \kappa/7` and $`|\scos(x)-\cos(x)|\leq \kappa/7`.
:::

:::proof "lem:kappa7" (leanok := true)
Using {uses "lem:sin27cos26"}[].
Straightforward numerical computation.
:::

:::lemma_ "lem:A_le_deltamn" (lean := "RationalApprox.norm_le_delta_sqrt_dims") (parent := "rational_matrix_error")
Let $`A = (a_{i,j})_{1 \leq i \leq m,\,1 \leq j \leq n} \in \mathbb{R}^{m \times n}` and $`\delta >0`.
If $`|a_{i,j}| \leq \delta` for all entries, then $`\|A\| \leq \delta \sqrt{mn}`.
:::

:::proof "lem:A_le_deltamn" (leanok := true)
Standard norm estimate via Cauchy-Schwarz.
:::

:::lemma_ "lem:dist_le_kappa" (lean := "RationalApprox.norm_matrix_actual_approx_le_kappa") (parent := "rational_matrix_error")
Let $`A(x,y)` be an $`m\times n` matrix ($`1\le m,n\le 3`) whose entries are products of terms in
$`\{0,1,-1,\pm\sin(z),\pm\cos(z)\}`.
Let $`A_\mathbb{Q}(x,y)` be obtained by replacing $`\sin,\cos` with $`\ssin,\scos`.
Then for $`x,y\in[-4,4]`, $`\|A(x,y)-A_{\mathbb{Q}}(x,y)\|\leq\kappa`.
:::

:::proof "lem:dist_le_kappa" (leanok := true)
Using {uses "lem:kappa7"}[] and {uses "lem:A_le_deltamn"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 40)}[].
:::

:::corollary "corr:kappa1kappa" (lean := "RationalApprox.R_difference_norm_bounded,RationalApprox.R'_difference_norm_bounded,RationalApprox.M_difference_norm_bounded,RationalApprox.Mθ_difference_norm_bounded,RationalApprox.Mφ_difference_norm_bounded,RationalApprox.X_difference_norm_bounded,RationalApprox.Rℚ_norm_bounded,RationalApprox.Mℚ_norm_bounded") (parent := "rational_matrix_error")
Let $`\alpha,\theta,\phi\in[-4,4]`.
Then
$`\|R(\alpha)-R_\mathbb{Q}(\alpha)\|`,
$`\|R'(\alpha)-R'_\mathbb{Q}(\alpha)\|`,
$`\|X(\theta,\phi)-X_\mathbb{Q}(\theta,\phi)\|`,
$`\|M(\theta,\phi)-M_\mathbb{Q}(\theta,\phi)\|`,
$`\|M^\theta(\theta,\phi)-M^\theta_\mathbb{Q}(\theta,\phi)\|`,
$`\|M^\phi(\theta,\phi)-M^\phi_\mathbb{Q}(\theta,\phi)\|`
are all at most $`\kappa`.
Moreover $`\|R_\mathbb{Q}(\alpha)\|,\|M_\mathbb{Q}(\theta,\phi)\|\leq 1+\kappa`.
:::

:::proof "corr:kappa1kappa" (leanok := true)
Using {uses "lem:dist_le_kappa"}[] and {uses "lem:RaRalpha"}[].
:::

:::lemma_ "lem:A1AnB1Bn" (lean := "RationalApprox.norm_sub_le_prod") (parent := "rational_matrix_error")
Let $`(A_i,B_i)` for $`1\le i\le n` be pairs of same-size real matrices,
with products $`A_1\cdots A_n` and $`B_1\cdots B_n` defined.
If $`\|A_i-B_i\|\leq \kappa` and
$`\delta_i\geq \max(\|A_i\|,\|B_i\|,1)`,
then
$`\|A_1\cdots A_n-B_1\cdots B_n\|\leq n\kappa\,\delta_1\cdots\delta_n`.
:::

:::proof "lem:A1AnB1Bn" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 42)}[].
:::

:::lemma_ "lem:boundskappa" (lean := "RationalApprox.bounds_kappa_M,RationalApprox.bounds_kappa_Mθ,RationalApprox.bounds_kappa_Mφ,RationalApprox.bounds_kappa_RM,RationalApprox.bounds_kappa_R'M,RationalApprox.bounds_kappa_RMθ,RationalApprox.bounds_kappa_RMφ") (parent := "rational_matrix_error")
Let $`\alpha,\theta,\phi \in [-4,4]`, $`P\in \mathbb{R}^3` with $`\|P\| \leq 1`,
let $`\widetilde{P}` be a $`\kappa`-rational approximation, and let $`w \in \mathbb{R}^2` be unit.
Then the seven quantitative bounds (equations (1)-(7) in Lemma 44 of the paper)
hold for inner products involving $`M,M^\theta,M^\phi,R,R'` and their rational versions.
:::

:::proof "lem:boundskappa" (leanok := true)
Using {uses "lem:A1AnB1Bn"}[] and {uses "corr:kappa1kappa"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 44)}[].
:::

:::theorem "thm:global_rational" (lean := "RationalApprox.GlobalTheorem.rational_global") (parent := "rational_global_transfer")
Let $`\mathbf{P}` be a pointsymmetric convex polyhedron of radius 1,
and $`\widetilde{\mathbf{P}}` a $`\kappa`-rational approximation.
Define $`G^\mathbb{Q}` and $`H^\mathbb{Q}_P` as in the paper.
If $`G^\mathbb{Q}>\max_{P\in\widetilde{\mathbf{P}}} H^\mathbb{Q}_P` then there is no Rupert solution to $`\mathbf{P}`
in the interval
$`[\bar\theta_1\pm\epsilon,\bar\phi_1\pm\epsilon,\bar\theta_2\pm\epsilon,\bar\phi_2\pm\epsilon,\bar\alpha\pm\epsilon]`.
:::

:::proof "thm:global_rational" (leanok := true)
Using {uses "thm:global"}[] and {uses "lem:boundskappa"}[].
:::

:::definition "def:ekspanning" (parent := "rational_local_approx")
Let $`\theta, \phi \in \mathbb{Q} \cap [-4,4]` and
$`M_\mathbb{Q} := M_\mathbb{Q}(\theta, \phi)`.
Three points $`\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3 \in \mathbb{Q}^3`
with norms at most $`1+\kappa` are called
$`\epsilon`-$`\kappa`-spanning if the three inequalities in Definition 45 hold,
i.e. the spanning lower bounds include the extra additive $`6\kappa` term.
:::

:::lemma_ "lem:ekspanningespanning" (lean := "RationalApprox.ek_spanning_imp_e_spanning") (parent := "rational_local_approx")
Using {uses "def:ekspanning"}[].

Let $`P_1,P_2,P_3\in\mathbb{R}^3` with $`\|P_i\|\le 1`,
and $`\widetilde{P}_1,\widetilde{P}_2,\widetilde{P}_3\in\mathbb{Q}^3` be $`\kappa`-approximations.
If the rational points are $`\epsilon`-$`\kappa`-spanning,
then the original points are $`\epsilon`-spanning.
:::

:::proof "lem:ekspanningespanning" (leanok := true)
Using {uses "lem:A1AnB1Bn"}[], {uses "lem:eps-spanning"}[], and {uses "corr:kappa1kappa"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 46)}[].
:::

:::lemma_ "lem:boundskappa3" (lean := "RationalApprox.bounds_kappa3_X,RationalApprox.bounds_kappa3_M,RationalApprox.bounds_kappa3_MQ") (parent := "rational_local_approx")
Let $`P,Q \in \mathbb{R}^3` with $`\|P\|,\|Q\|\leq 1`,
and let $`\widetilde{P},\widetilde{Q}` be $`\kappa`-approximations.
Then, for parameters in $`[-4,4]`,

- $`|\langle X, P \rangle - \langle X_{\mathbb{Q}}, \widetilde{P} \rangle| \leq 3\kappa`
- $`|\langle MP, MQ \rangle - \langle M_{\mathbb{Q}}\widetilde{P}, M_{\mathbb{Q}}\widetilde{Q} \rangle| \leq 5\kappa`
- $`|\| M Q \| - \| M_{\mathbb{Q}}\widetilde{Q} \| | \leq 3\kappa`
:::

:::proof "lem:boundskappa3" (leanok := true)
Using {uses "lem:A1AnB1Bn"}[].
See {citet polyhedron.without.rupert (kind := lemma) (index := 49)}[].
:::

:::corollary "corr:deltakappa" (lean := "RationalApprox.delta_kappa") (parent := "rational_local_approx")
In the setting of {uses "lem:boundskappa3"}[], let additionally
$`\bar\theta,\bar\phi \in [-4,4]` and define
$`\overline{M} = M(\bar\theta, \bar\phi)`,
$`\overline{M}_{\mathbb{Q}} = M_{\mathbb{Q}}(\bar\theta, \bar\phi)`.
Then

$$`
\big|\|R(\alpha) M P - \overline{M} Q\|- \| R_{\mathbb{Q}}(\alpha) M_{\mathbb{Q}} \widetilde{P} - \overline{M}_{\mathbb{Q}} \widetilde{Q}\| \big| \leq 6 \kappa.
`
:::

:::proof "corr:deltakappa" (leanok := true)
Using {uses "lem:boundskappa3"}[].
See {citet polyhedron.without.rupert (kind := corollary) (index := 50)}[].
:::

:::corollary "lem:boundskappa4" (lean := "RationalApprox.bounds_kappa4") (parent := "rational_local_approx")
In the setting of {uses "lem:boundskappa3"}[], define the real quantity $`A`
and rational lower surrogate $`A_{\mathbb{Q}}` as in Corollary 51.
Then $`A \geq A_{\mathbb{Q}}`.
:::

:::proof "lem:boundskappa4" (leanok := true)
Using {uses "lem:boundskappa3"}[].
See {citet polyhedron.without.rupert (kind := corollary) (index := 51)}[].
:::

:::theorem "thm:local_rational" (lean := "RationalApprox.LocalTheorem.rational_local") (parent := "rational_local_transfer")
Using {uses "def:ekspanning"}[].

Let $`\mathbf{P}` be a polyhedron with radius 1 and let
$`\widetilde{P}_i` be a $`\kappa`-rational approximation of each
$`P_i \in \mathbf{P}`.
Assume the rational hypotheses $`(A^\mathbb{Q}_\epsilon)` and
$`(B^\mathbb{Q}_\epsilon)` from the paper, together with
$`\epsilon`-$`\kappa`-spanning conditions for both triples.
Then there is no Rupert solution in
$`[\bar\theta_1\pm\epsilon,\bar\phi_1\pm\epsilon,\bar\theta_2\pm\epsilon,\bar\phi_2\pm\epsilon,\bar\alpha\pm\epsilon]`.
:::

:::proof "thm:local_rational" (leanok := true)
Using {uses "thm:local"}[], {uses "lem:boundskappa3"}[], {uses "lem:boundskappa4"}[],
{uses "corr:deltakappa"}[], and {uses "lem:ekspanningespanning"}[].
:::
