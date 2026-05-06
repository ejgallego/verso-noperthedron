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
open Noperthedron

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

```tex
\begin{definition} \label{dfn:sin_cos_approx}
\leanok
\lean{RationalApprox.sinℚ,RationalApprox.cosℚ}
    We define the two functions $\ssin, \scos: \R \to \R$ by:
    \begin{align*}
    \ssin(x) & \coloneqq x-\frac{x^3}{3}+\frac{x^5}{5!}\mp \dots +\frac{x^{25}}{25!},\\
    \scos(x) & \coloneqq 1-\frac{x^2}{2}+\frac{x^4}{4!}\mp\dots +\frac{x^{24}}{24!}.
    \end{align*}
    Further, by replacing $\sin,\cos$ with $\ssin,\scos$ we define the functions
\[
    R_{\Q}(\alpha), R'_{\Q}(\alpha), X_{\Q}(\theta, \phi), M_{\Q}(\theta, \phi), M_{\Q}^{\theta}(\theta,\varphi),M_{\Q}^{\phi}(\theta,\varphi).
\]
\end{definition}
```

:::lemma_ "lem:sin27cos26" (lean := "RationalApprox.sinℚ_approx,RationalApprox.cosℚ_approx") (parent := "rational_trig_approx")
Using {uses "dfn:sin_cos_approx"}[].

$$`
|\ssin(x)-\sin(x)|\leq \frac{|x|^{27}}{27!}
\qquad\text{and}\qquad
|\scos(x)-\cos(x)|\leq \frac{|x|^{26}}{26!}.
`
:::

```tex
\begin{lemma} \label{lem:sin27cos26}
\leanok
\lean{RationalApprox.sinℚ_approx,RationalApprox.cosℚ_approx}
    \[
        |\ssin(x)-\sin(x)|\leq \frac{|x|^{27}}{27!} \quad \text{and} \quad
    |\scos(x)-\cos(x)|\leq \frac{|x|^{26}}{26!}.
    \]
\uses{dfn:sin_cos_approx}
\end{lemma}
```

:::proof "lem:sin27cos26"
Appeal to Taylor series bounds, using the fact that all absolute values of
higher derivatives of sine and cosine never exceed 1.
:::

```tex
\begin{proof}
\leanok
Appeal to Taylor series bounds, using the fact that all absolute values of
higher derivatives of sine and cosine never exceed 1.
\end{proof}
```

:::lemma_ "lem:kappa7" (lean := "RationalApprox.sinℚ_approx',RationalApprox.cosℚ_approx'") (parent := "rational_trig_approx")
For every $`x\in [-4,4]`,
$`|\ssin(x)-\sin(x)| \leq \kappa/7` and $`|\scos(x)-\cos(x)|\leq \kappa/7`.
:::

```tex
\begin{lemma} \label{lem:kappa7}
\leanok
\lean{RationalApprox.sinℚ_approx',RationalApprox.cosℚ_approx'}
    For every $x\in [-4,4]$ it holds that
    \[
    |\ssin(x)-\sin(x)| \leq \frac{\kappa}{7} \quad \text{and} \quad |\scos(x)-\cos(x)|\leq \frac{\kappa}{7}.
    \]
\end{lemma}
```

:::proof "lem:kappa7"
Using {uses "lem:sin27cos26"}[].
Straightforward numerical calculation from Lemma {uses "lem:sin27cos26"}[].
:::

```tex
\begin{proof}
\uses{lem:sin27cos26}
\leanok
Straightforward numerical calculation from Lemma~\ref{lem:sin27cos26}.
\end{proof}
```

:::lemma_ "lem:A_le_deltamn" (lean := "RationalApprox.norm_le_delta_sqrt_dims") (parent := "rational_matrix_error")
Let $`A = (a_{i,j})_{1 \leq i \leq m,\,1 \leq j \leq n} \in \mathbb{R}^{m \times n}` and $`\delta >0`.
If $`|a_{i,j}| \leq \delta` for all entries, then $`\|A\| \leq \delta \sqrt{mn}`.
:::

```tex
\begin{lemma} \label{lem:A_le_deltamn}
  \lean{RationalApprox.norm_le_delta_sqrt_dims}
  \leanok
Let $A = (a_{i,j})_{1 \leq i \leq m,\ 1 \leq j \leq n} \in \R^{m \times n}$ and $\delta >0$. Assume that $|a_{i,j}| \leq \delta$. Then it holds that $\|A\| \leq \delta \sqrt{mn}.$
\end{lemma}
```

:::proof "lem:A_le_deltamn"
For any $`v\in \R^n` we have

$$`
\begin{align*}
\|Av\|^2 &=\sum_{i=1}^m \left(\sum_{j=1}^na_{i,j}v_j\right)^2 \leq \sum_{i=1}^m\left(\sum_{j=1}^n \delta |v_j|\right)^2 = \delta^2 m\left(\sum_{j=1}^n |v_j|\right)^2 \leq \delta^2 m n \|v\|^2
\end{align*}
`
$$

using the Cauchy-Schwarz inequality. Dividing by $`\|v\|` and taking the square root proves the claim.
:::

```tex
\begin{proof}
\leanok
    For any $v\in \R^n$ we have
    \begin{align*}
        \|Av\|^2 &=\sum_{i=1}^m \left(\sum_{j=1}^na_{i,j}v_j\right)^2 \leq \sum_{i=1}^m\left(\sum_{j=1}^n \delta |v_j|\right)^2 = \delta^2 m\left(\sum_{j=1}^n |v_j|\right)^2 \leq \delta^2 m n \|v\|^2
    \end{align*}
    using the Cauchy-Schwarz inequality. Dividing by $\|v\|$ and taking the square root proves the claim.
\end{proof}
```

:::lemma_ "lem:dist_le_kappa" (lean := "RationalApprox.norm_matrix_actual_approx_le_kappa") (parent := "rational_matrix_error")
Let $`A(x,y)` be an $`m\times n` matrix ($`1\le m,n\le 3`) whose entries are products of terms in
$`\{0,1,-1,\pm\sin(z),\pm\cos(z)\}`.
Let $`A_\mathbb{Q}(x,y)` be obtained by replacing $`\sin,\cos` with $`\ssin,\scos`.
Then for $`x,y\in[-4,4]`, $`\|A(x,y)-A_{\mathbb{Q}}(x,y)\|\leq\kappa`.
:::

```tex
\begin{lemma}\label{lem:dist_le_kappa}
\leanok
\lean{RationalApprox.norm_matrix_actual_approx_le_kappa}
    Let $A(x,y)$ be an $m\times n$ matrix with $1 \leq m,n\leq 3$ such that every entry is of the form $a_1(x)\cdot a_2(y)$ where
    $a_i(z)\in \{0,1,-1,\pm\sin(z),\pm\cos(z)\}.$
    Define $A_{\mathbb{Q}}(x,y)$ by replacing $\sin$ with $\ssin$ and $\cos$ with $\scos$. Then for every $x,y\in[-4,4]$ it holds that
    $\|A(x,y)-A_{\mathbb{Q}}(x,y)\|\leq\kappa$.
\end{lemma}
```

:::proof "lem:dist_le_kappa"
Using {uses "lem:kappa7"}[] and {uses "lem:A_le_deltamn"}[].
We've replaced the assumption $`a_i(z)\in \{0,1,-1,\pm\sin(z),\pm\cos(z)\}` in
{citet polyhedron.without.rupert}[]'s Lemma 40 with $`a_i(z)\in [-1,1]`.

By assumption, for fixed $`x,y` every entry of $`A(x,y)-A_{\mathbb{Q}}(x,y)` is of the form
$`a b - \widetilde{a}\widetilde{b}` for some $`a,b\in[-1,1]` and
$`|a-\widetilde{a}|,|b-\widetilde{b}|\leq \kappa/7` by {uses "lem:kappa7"}[].
This implies that

$$`
\begin{align*}
|ab-\widetilde{a}\widetilde{b}|&\leq |a b-a\widetilde{b}|+|a \widetilde{b}-\widetilde{a}\widetilde{b}| \\
&=|a|\cdot |b-\widetilde{b}|+|\widetilde{b}|\cdot |a-\widetilde{a}| \leq 1\cdot \kappa/7+(1+\kappa/7) \cdot \kappa/7 <\kappa/3.
\end{align*}
`
$$

So we can apply {uses "lem:A_le_deltamn"}[] and obtain that
$`\|A(x,y)-A_{\Q}(x,y)\|<\kappa/3\cdot \sqrt{3\cdot 3}=\kappa`.
:::

```tex
\begin{proof}
\leanok
\uses{lem:kappa7,lem:A_le_deltamn}
    We've replaced the assumption $a_i(z)\in \{0,1,-1,\pm\sin(z),\pm\cos(z)\}$ in \cite{polyhedron.without.rupert}'s
    Lemma~40 with $a_i(z)\in [-1,1]$.

    By assumption, for fixed $x,y$ every entry of $A(x,y)-A_{\mathbb{Q}}(x,y)$ is of the form
    $a b - \widetilde{a}\widetilde{b}$ for some $a,b\in[-1,1]$ and $|a-\widetilde{a}|,|b-\widetilde{b}|\leq \kappa/7$ by \cref{lem:kappa7}. This implies that
    \begin{align*}
      |ab-\widetilde{a}\widetilde{b}|&\leq |a b-a\widetilde{b}|+|a \widetilde{b}-\widetilde{a}\widetilde{b}|
      =|a|\cdot |b-\widetilde{b}|+|\widetilde{b}|\cdot |a-\widetilde{a}| \leq 1\cdot \kappa/7+(1+\kappa/7) \cdot \kappa/7 <\kappa/3.
    \end{align*}
    So we can apply \cref{lem:A_le_deltamn} and obtain that $\|A(x,y)-A_{\Q}(x,y)\|<\kappa/3\cdot \sqrt{3\cdot 3}=\kappa$.
\end{proof}
```

:::corollary "corr:kappa1kappa" (lean := "RationalApprox.R_difference_norm_bounded,RationalApprox.R'_difference_norm_bounded,RationalApprox.M_difference_norm_bounded,RationalApprox.Mθ_difference_norm_bounded,RationalApprox.Mφ_difference_norm_bounded,RationalApprox.X_difference_norm_bounded,RationalApprox.Rℚ_norm_bounded,RationalApprox.Mℚ_norm_bounded,RationalApprox.R'ℚ_norm_bounded,RationalApprox.Mθℚ_norm_bounded,RationalApprox.Mφℚ_norm_bounded") (parent := "rational_matrix_error")
Let $`\alpha,\theta,\phi\in[-4,4]`.
Then
$`\|R(\alpha)-R_\mathbb{Q}(\alpha)\|`,
$`\|R'(\alpha)-R'_\mathbb{Q}(\alpha)\|`,
$`\|X(\theta,\phi)-X_\mathbb{Q}(\theta,\phi)\|`,
$`\|M(\theta,\phi)-M_\mathbb{Q}(\theta,\phi)\|`,
$`\|M^\theta(\theta,\phi)-M^\theta_\mathbb{Q}(\theta,\phi)\|`,
$`\|M^\phi(\theta,\phi)-M^\phi_\mathbb{Q}(\theta,\phi)\|`
are all at most $`\kappa`.
Moreover $`\|R_\mathbb{Q}(\alpha)\|, \|R'_\mathbb{Q}(\alpha)\|, \|M_\mathbb{Q}(\theta, \phi)\|, \|M_{\Q}^{\theta}(\theta,\varphi)\|, \|M_{\Q}^{\phi}(\theta,\varphi)\| \leq 1+\kappa`.
:::

```tex
\begin{corollary} \label{corr:kappa1kappa}
\leanok
\lean{
RationalApprox.R_difference_norm_bounded,
RationalApprox.R'_difference_norm_bounded,
RationalApprox.M_difference_norm_bounded,
RationalApprox.Mθ_difference_norm_bounded,
RationalApprox.Mφ_difference_norm_bounded,
RationalApprox.X_difference_norm_bounded,
RationalApprox.Rℚ_norm_bounded,
RationalApprox.Mℚ_norm_bounded,
RationalApprox.R'ℚ_norm_bounded,
RationalApprox.Mθℚ_norm_bounded,
RationalApprox.Mφℚ_norm_bounded }
    Let $\alpha,\theta,\phi\in [-4,4]$. Then it holds that
    \begin{align*}
        \|R(\alpha)-R_{\Q}(\alpha)\|, \|R'(\alpha)-R_{\Q}'(\alpha)\|,\|X(\theta,\phi)-X_{\Q}(\theta, \phi)\|, \|M(\theta, \phi)-M_{\Q}(\theta, \phi)\|, \\
        \|M^\theta(\theta,\phi)-M_{\Q}^\theta(\theta,\phi)\|,
        \|M^\phi(\theta,\phi) - M_{\Q}^\phi(\theta,\phi)\|\leq \kappa.
    \end{align*}
    Moreover,
    \[
        \|R_{\Q}(\alpha)\|, \|R'_{\Q}(\alpha)\|, \|M_{\Q}(\theta, \phi)\|, \|M_{\Q}^{\theta}(\theta,\varphi)\|, \|M_{\Q}^{\phi}(\theta,\varphi)\| \leq 1+\kappa
    \]
\end{corollary}
```

:::proof "corr:kappa1kappa"
Using {uses "lem:dist_le_kappa"}[] and {uses "lem:RaRalpha"}[].

The first statement is a direct application of {uses "lem:dist_le_kappa"}[] and the second statement follows immediately after using {uses "lem:RaRalpha"}[] and the triangle inequality.
The derivative norm bounds follow similarly, using that the operator norms of $`R'`, $`M^\theta`, and $`M^\phi` are at most $`1`.
:::

```tex
\begin{proof}
\leanok
\uses{lem:dist_le_kappa,lem:RaRalpha}
    The first statement is a direct application of \cref{lem:dist_le_kappa} and the second statement follows immediately after using \cref{lem:RaRalpha} and the triangle inequality.
    The derivative norm bounds follow similarly, using that the operator norms of $R'$, $M^\theta$, and $M^\phi$ are at most~$1$.
\end{proof}
```

:::lemma_ "lem:A1AnB1Bn" (lean := "RationalApprox.norm_sub_le_prod") (parent := "rational_matrix_error")
Let $`(A_i,B_i)` for $`1\le i\le n` be pairs of same-size real matrices,
with products $`A_1\cdots A_n` and $`B_1\cdots B_n` defined.
If $`\|A_i-B_i\|\leq \kappa` and
$`\delta_i\geq \max(\|A_i\|,\|B_i\|,1)`,
then
$`\|A_1\cdots A_n-B_1\cdots B_n\|\leq n\kappa\,\delta_1\cdots\delta_n`.
:::

```tex
\begin{lemma} \label{lem:A1AnB1Bn}
\lean{RationalApprox.norm_sub_le_prod}
\leanok
    For $1 \leq i \leq n$ let $(A_i,B_i)$ be pairs of real matrices, such that for each $i$ the dimensions of $A_i$ and $B_i$ are equal. Assume moreover that the products $A_1\cdots A_n$ and $B_1 \cdots B_n$ are well defined. Finally, assume that $\|A_i-B_i\|\leq \kappa$ and let $\delta_i\geq \max(\|A_i\|,\|B_i\|,1)$. Then it holds that
    $\|A_1\cdots A_n-B_1\cdots B_n\|\leq n\kappa\cdot \delta_1\cdots \delta_n$.
\end{lemma}
```

:::proof "lem:A1AnB1Bn"
See polyhedron.without.rupert, Lemma 42.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 42.
\end{proof}
```

:::lemma_ "lem:boundskappa" (lean := "RationalApprox.bounds_kappa_M,RationalApprox.bounds_kappa_Mθ,RationalApprox.bounds_kappa_Mφ,RationalApprox.bounds_kappa_RM,RationalApprox.bounds_kappa_R'M,RationalApprox.bounds_kappa_RMθ,RationalApprox.bounds_kappa_RMφ") (parent := "rational_matrix_error")
Let $`\alpha, \theta, \phi \in [-4,4]`, $`P\in \R^3` with $`\|P\| \leq 1`
and let $`\widetilde{P}` be a $`\kappa`-rational approximation of $`P`.
Set $`M = M(\theta, \phi)` and $`M_{\Q} = M_{\Q}(\theta, \phi)`,
$`M^\theta = M^\theta(\theta, \phi)` and $`M^\theta_{\Q} = M^\theta_{\Q}(\theta, \phi)`,
$`M^\phi = M^\phi(\theta, \phi)` and $`M^\phi_{\Q} = M^\phi_{\Q}(\theta, \phi)`,
as well as $`R = R(\alpha)`, $`R_{\Q} = R_{\Q}(\alpha)`, $`R' = R'(\alpha)`,
$`R'_{\Q} = R'_{\Q}(\alpha)`.
Finally let $`w \in \R^2` with $`\|w\| = 1`.
Then:

$$`
\begin{align}
| \langle M P, w\rangle - \langle M_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa \\
| \langle M^\theta P, w\rangle - \langle M^\theta_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa,\\
| \langle M^\phi P, w\rangle - \langle M^\phi_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa,\\
| \langle R M P, w\rangle - \langle R_{\Q} M_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa \\
| \langle R' M P, w\rangle - \langle R'_{\Q} M_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa,\\
| \langle R M^\theta P, w\rangle - \langle R_{\Q} M^\theta_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa,\\
| \langle R M^\phi P, w\rangle - \langle R_{\Q} M^\phi_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa.
\end{align}
`
$$
:::

```tex
\begin{lemma} \label{lem:boundskappa}
\leanok
\lean{
RationalApprox.bounds_kappa_M,
RationalApprox.bounds_kappa_Mθ,
RationalApprox.bounds_kappa_Mφ,
RationalApprox.bounds_kappa_RM,
RationalApprox.bounds_kappa_R'M,
RationalApprox.bounds_kappa_RMθ,
RationalApprox.bounds_kappa_RMφ
}
    Let $\alpha, \theta, \phi \in [-4,4]$, $P\in \R^3$ with $\|P\| \leq 1$ and let $\widetilde{P}$ be a $\kappa$-rational approximation of $P$. Set $M = M(\theta, \phi)$ and $M_{\Q} = M_{\Q}(\theta, \phi)$, $M^\theta = M^\theta(\theta, \phi)$, $M^\theta_{\Q} = M^\theta_{\Q}(\theta, \phi)$, $M^\phi = M^\phi(\theta, \phi)$, $M^\phi_{\Q} = M^\phi_{\Q}(\theta, \phi)$ as well as $R = R(\alpha)$, $R_{\Q} = R_{\Q}(\alpha)$, $R' = R'(\alpha)$, $R'_{\Q} = R'_{\Q}(\alpha)$. Finally let $w \in \R^2$ with $\|w\| = 1$. Then:
    \begin{align}
        | \langle M P, w\rangle - \langle M_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa, \label{eq:boundskappa1} \\
        | \langle M^\theta P, w\rangle - \langle M^\theta_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa,\\
        | \langle M^\phi P, w\rangle - \langle M^\phi_{\Q} \widetilde{P}, w\rangle | & \leq 3\kappa,\\
        | \langle R M P, w\rangle - \langle R_{\Q} M_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa,\label{eq:boundskappa4} \\
        | \langle R' M P, w\rangle - \langle R'_{\Q} M_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa,\\
        | \langle R M^\theta P, w\rangle - \langle R_{\Q} M^\theta_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa,\\
        | \langle R M^\phi P, w\rangle - \langle R_{\Q} M^\phi_{\Q} \widetilde{P}, w\rangle | & \leq 4\kappa.
    \end{align}
\end{lemma}
```

:::proof "lem:boundskappa"
Using {uses "lem:A1AnB1Bn"}[] and {uses "corr:kappa1kappa"}[].
See polyhedron.without.rupert, Lemma 44.
:::

```tex
\begin{proof}
\leanok
\uses{lem:A1AnB1Bn,corr:kappa1kappa}
See \cite{polyhedron.without.rupert}, Lemma 44.
\end{proof}
```

:::theorem "thm:global_rational" (lean := "RationalApprox.GlobalTheorem.rational_global") (parent := "rational_global_transfer")
Let $`\PPP` be a pointsymmetric convex polyhedron with radius $`\rho =1` and
$`\widetilde{\PPP}` a $`\kappa`-rational approximation. Let $`\widetilde{S} \in \widetilde{\PPP}`.
Further let $`\epsilon>0` and $`\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \Q \cap [-4,4]`.
Let $`w\in\Q^2` be a unit vector. Denote $`\Mib \coloneqq M_{\Q}(\thetab_1, \phib_1)`,
$`\Miib \coloneqq M_{\Q}(\thetab_2, \phib_2)` as well as
$`\Mib^{\theta} \coloneqq M_{\Q}^\theta(\thetab_1, \phib_1)`,
$`\Mib^{\phi} \coloneqq M_{\Q}^\phi(\thetab_1, \phib_1)` and analogously for
$`\Miib^{\theta}, \Miib^{\phi}`. Finally set

$$`
\begin{align*}
G^{\Q}& \coloneqq \langle R_{\Q}(\alphab) \Mib \widetilde{S},w \rangle - \epsilon\cdot\big(|\langle R_{\Q}'(\alphab)  \Mib \widetilde{S},w \rangle|+|\langle R_{\Q}(\alphab) \Mib^\theta \widetilde{S},w \rangle|+|\langle R_{\Q}(\alphab) \Mib^\phi \widetilde{S},w \rangle|\big) \\
& \hspace{11cm}- 9\epsilon^2/2 - 4\kappa ( 1 + 3 \epsilon),\\
H^{\Q}_P & \coloneqq \langle \Miib P,w \rangle + \epsilon\cdot\big(|\langle \Miib^\theta P,w \rangle|+|\langle  \Miib^\varphi P,w \rangle|\big) + 2\epsilon^2 + 3\kappa( 1+2\epsilon).
\end{align*}
`
$$

If $`G^{\Q}>\max_{P\in \widetilde{\PPP}} H^{\Q}_P` then there does not exist a solution to Rupert's condition to $`\PPP` with

$$`
(\theta_1,\varphi_1,\theta_2,\varphi_2,\alpha) \in [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon].
`
$$
:::

```tex
\begin{theorem}[Rational Global Theorem] \label{thm:global_rational}
\leanok
\lean{RationalApprox.GlobalTheorem.rational_global}
    Let $\PPP$ be a pointsymmetric convex polyhedron with radius $\rho =1$ and $\widetilde{\PPP}$ a $\kappa$-rational approximation. Let $\widetilde{S} \in \widetilde{\PPP}$. Further let $\epsilon>0$ and $\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \Q \cap [-4,4]$.
    Let $w\in\Q^2$ be a unit vector. Denote $\Mib \coloneqq M_{\Q}(\thetab_1, \phib_1)$, $ \Miib \coloneqq M_{\Q}(\thetab_2, \phib_2)$ as well as $\Mib^{\theta} \coloneqq M_{\Q}^\theta(\thetab_1, \phib_1)$, $\Mib^{\phi} \coloneqq M_{\Q}^\phi(\thetab_1, \phib_1)$ and analogously for $\Miib^{\theta}, \Miib^{\phi}$. Finally set
    \begin{align*}
        G^{\Q}& \coloneqq \langle R_{\Q}(\alphab) \Mib \widetilde{S},w \rangle - \epsilon\cdot\big(|\langle R_{\Q}'(\alphab)  \Mib \widetilde{S},w \rangle|+|\langle R_{\Q}(\alphab) \Mib^\theta \widetilde{S},w \rangle|+|\langle R_{\Q}(\alphab) \Mib^\phi \widetilde{S},w \rangle|\big) \\
        & \hspace{11cm}- 9\epsilon^2/2 - 4\kappa ( 1 + 3 \epsilon),\\
        H^{\Q}_P & \coloneqq \langle \Miib P,w \rangle + \epsilon\cdot\big(|\langle \Miib^\theta P,w \rangle|+|\langle  \Miib^\varphi P,w \rangle|\big) + 2\epsilon^2 + 3\kappa( 1+2\epsilon).
    \end{align*}
    If $G^{\Q}>\max_{P\in \widetilde{\PPP}} H^{\Q}_P$ then there does not exist a solution to Rupert's condition to $\PPP$ with
    \[
    (\theta_1,\varphi_1,\theta_2,\varphi_2,\alpha) \in [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon].
    \]
\end{theorem}
```

:::proof "thm:global_rational"
{uses "thm:global"}[] {uses "lem:boundskappa"}[]
:::

```tex
\begin{proof}
\leanok
\uses{thm:global,lem:boundskappa}
\end{proof}
```

:::definition "def:ekspanning" (lean := "Local.Triangle.κSpanning") (parent := "rational_local_approx")
Let $`\theta, \phi \in \Q \cap [-4,4]` and $`M_{\Q} \coloneqq M_{\Q}(\theta, \phi)`.
Three points $`\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3 \in \Q^3`
with $`\|\widetilde{P}_1\|, \|\widetilde{P}_2\|, \|\widetilde{P}_3\| \leq 1+\kappa`
are called $`\epsilon`-$`\kappa`-spanning for $`(\theta, \phi)` if it holds that:

$$`
\begin{align*}
\langle R(\pi/2) M_{\Q} \widetilde{P}_1,M_{\Q} \widetilde{P}_{2}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa,\\
\langle R(\pi/2) M_{\Q} \widetilde{P}_2,M_{\Q} \widetilde{P}_{3}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa,\\
\langle R(\pi/2) M_{\Q} \widetilde{P}_3,M_{\Q} \widetilde{P}_{1}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa.
\end{align*}
`
$$
:::

```tex
\begin{definition} \label{def:ekspanning}
\leanok
\lean{Local.Triangle.κSpanning}
    Let $\theta, \phi \in \Q \cap [-4,4]$ and $M_{\Q} \coloneqq M_{\Q}(\theta, \phi)$. Three points $\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3 \in \Q^3$ with $\|\widetilde{P}_1\|, \|\widetilde{P}_2\|, \|\widetilde{P}_3\| \leq 1+\kappa$ are called \emph{$\epsilon$-$\kappa$-spanning for $(\theta, \phi)$} if it holds that:
\begin{align*}
    \langle R(\pi/2) M_{\Q} \widetilde{P}_1,M_{\Q} \widetilde{P}_{2}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa,\\
    \langle R(\pi/2) M_{\Q} \widetilde{P}_2,M_{\Q} \widetilde{P}_{3}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa,\\
    \langle R(\pi/2) M_{\Q} \widetilde{P}_3,M_{\Q} \widetilde{P}_{1}\rangle > 2 \epsilon(\sqrt{2} + \epsilon) + 6\kappa.
\end{align*}
\end{definition}
```

:::lemma_ "lem:ekspanningespanning" (lean := "RationalApprox.ek_spanning_imp_e_spanning") (parent := "rational_local_approx")
Using {uses "def:ekspanning"}[].

Let $`P_1, P_2, P_3 \in \R^3` with $`\|P_i\| \leq 1`
and $`\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3 \in \Q^3`
be their $`\kappa`-rational approximations.
Assume that $`\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3` are
$`\epsilon`-$`\kappa`-spanning for some $`\theta, \phi \in \Q \cap [-4,4]`,
then $`P_1, P_2, P_3` are $`\epsilon`-spanning for $`\theta, \phi`.
:::

```tex
\begin{lemma} \label{lem:ekspanningespanning}
\leanok
\lean{RationalApprox.ek_spanning_imp_e_spanning}
\uses{def:ekspanning}
    Let $P_1, P_2, P_3 \in \R^3$ with $\|P_i\| \leq 1$ and $\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3 \in \Q^3$ be their $\kappa$-rational approximations. Assume that $\widetilde{P}_1, \widetilde{P}_2, \widetilde{P}_3$ are $\epsilon$-$\kappa$-spanning for some $\theta, \phi \in \Q \cap [-4,4]$, then $P_1, P_2, P_3$ are $\epsilon$-spanning for $\theta, \phi$.
\end{lemma}
```

:::proof "lem:ekspanningespanning"
Using {uses "lem:A1AnB1Bn"}[], {uses "lem:eps-spanning"}[], and {uses "corr:kappa1kappa"}[].
See polyhedron.without.rupert, Lemma 46.
:::

```tex
\begin{proof}
\leanok
\uses{lem:A1AnB1Bn,lem:eps-spanning,corr:kappa1kappa}
See \cite{polyhedron.without.rupert}, Lemma 46.
\end{proof}
```

:::lemma_ "lem:boundskappa3" (lean := "RationalApprox.bounds_kappa3_X,RationalApprox.bounds_kappa3_M,RationalApprox.bounds_kappa3_MQ") (parent := "rational_local_approx")
Let $`P,Q \in \mathbb{R}^3` with $`\|P\|,\|Q\|\leq 1`,
and let $`\widetilde{P},\widetilde{Q}` be $`\kappa`-approximations.
Then, for parameters in $`[-4,4]`,

- $`|\langle X, P \rangle - \langle X_{\mathbb{Q}}, \widetilde{P} \rangle| \leq 3\kappa`
- $`|\langle MP, MQ \rangle - \langle M_{\mathbb{Q}}\widetilde{P}, M_{\mathbb{Q}}\widetilde{Q} \rangle| \leq 5\kappa`
- $`|\| M Q \| - \| M_{\mathbb{Q}}\widetilde{Q} \| | \leq 3\kappa`
:::

```tex
\begin{lemma} \label{lem:boundskappa3}
\leanok
\lean{
RationalApprox.bounds_kappa3_X,
RationalApprox.bounds_kappa3_M,
RationalApprox.bounds_kappa3_MQ
}
    Let $P,Q \in \R^3$ with $\|P\|,\|Q\|\leq 1$ and $\widetilde{P},\widetilde{Q}$ some respective $\kappa$-rational approximations. Moreover, let $\alpha, \theta, \phi \in \R \in [-4,4]$ and set $X = X(\theta, \phi)$, $X_{\Q} = X_{\Q}(\theta, \phi)$ as well as $M = M(\theta, \phi)$, $M_{\Q} = M_{\Q}(\theta, \phi)$. Then
    \begin{align}
        |\langle X, P \rangle - \langle X_{\Q}, \widetilde{P} \rangle| & \leq 3 \kappa, \label{eq:boundskappa3.1}\\
        |\langle MP, MQ \rangle - \langle M_{\Q} \widetilde{P}, M_{\Q}\widetilde{Q} \rangle| & \leq 5 \kappa, \label{eq:boundskappa3.3}\\
        |\| M Q \| - \| M_{\Q}\widetilde{Q} \| | & \leq 3 \kappa.\label{eq:boundskappa3.2}
    \end{align}
\end{lemma}
```

:::proof "lem:boundskappa3"
Using {uses "lem:A1AnB1Bn"}[].
See polyhedron.without.rupert, Lemma 49.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 49.
\uses{lem:A1AnB1Bn}
\end{proof}
```

:::corollary "corr:deltakappa" (lean := "RationalApprox.delta_kappa") (parent := "rational_local_approx")
Let $`P, Q \in \R^3` with $`\|P\|, \|Q\| \leq 1` and
$`\widetilde{Q}` a $`\kappa`-rational approximation of $`Q`.
Let $`\alpha, \theta, \phi, \thetab, \phib \in [-4,4]` and set
$`M = M(\theta, \phi)`, $`M_{\Q} = M_{\Q}(\theta, \phi)`,
$`\overline{M} = M(\thetab, \phib)`, $`\overline{M}_{\Q} = M_{\Q}(\thetab, \phib)`.
Then

$$`
\big|\|R(\alpha) M P - \overline{M} Q\|- \| R_{\Q}(\alpha) M_{\Q} P - \overline{M}_{\Q} \widetilde{Q}\| \big| \leq 6 \kappa
`

Note that the rational side uses $`P` directly (not a rational approximation $`\widetilde{P}`).
:::

```tex
\begin{corollary} \label{corr:deltakappa}
\leanok
\lean{RationalApprox.delta_kappa}
    Let $P, Q \in \R^3$ with $\|P\|, \|Q\| \leq 1$ and $\widetilde{Q}$ a $\kappa$-rational approximation of $Q$.
    Let $\alpha, \theta, \phi, \thetab, \phib \in [-4,4]$ and set $M = M(\theta, \phi)$, $M_{\Q} = M_{\Q}(\theta, \phi)$, $\overline{M} = M(\thetab, \phib)$, $\overline{M}_{\Q} = M_{\Q}(\thetab, \phib)$. Then
     \[
|\|R(\alpha) M P - \overline{M} Q\|- \| R_{\Q}(\alpha) M_{\Q} P - \overline{M}_{\Q} \widetilde{Q}\| | \leq 6 \kappa
     \]
    Note that the rational side uses $P$ directly (not a rational approximation $\widetilde{P}$).
\end{corollary}
```

:::proof "corr:deltakappa"
{uses "corr:kappa1kappa"}[] {uses "lem:RaRalpha"}[]

See polyhedron.without.rupert, Corollary 50.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Corollary 50.
\uses{corr:kappa1kappa,lem:RaRalpha}
\end{proof}
```

:::corollary "lem:boundskappa4" (lean := "RationalApprox.bounds_kappa4") (parent := "rational_local_approx")
In the setting of Lemma 49, let $`\sqrt[+]{x}` be an upper square-root function, i.e.,
$`\sqrt{x} \leq \sqrt[+]{x}` for all real $`x \geq 0` with rational output on rational input.
Set $`\|x\|_{+} \coloneqq \sqrt[+]{\|x\|^2}`.
Set

$$`
A =  \frac{\langle M P, M(P-Q)\rangle - 2 \epsilon  \|P-Q\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\| M P\|+\sqrt{2} \varepsilon \big) \cdot \big(\|M(P-Q)\|+2 \sqrt{2} \varepsilon\big)}
`
$$

as well as

$$`
A_{\Q} =         \frac{\langle M_{\Q} \widetilde{P}, M_{\Q} (\widetilde{P}-\widetilde{Q})\rangle - 10\kappa - 2 \epsilon ( \|\widetilde{P}-\widetilde{Q}\| + 2 \kappa ) \cdot  (\sqrt{2}+\varepsilon)}{ \big(\| M_{\Q} \widetilde{P}\|_{+}+\sqrt{2} \varepsilon + 3\kappa \big) \cdot \big(\|M_{\Q}(\widetilde{P}-\widetilde{Q})\|_{+}+2 \sqrt{2} \varepsilon + 6\kappa\big)}.
`
$$

Assume that $`A \geq 0`.
Then $`A \geq A_{\mathbb{Q}}`.
:::

```tex
\begin{corollary} \label{lem:boundskappa4}
\leanok
\lean{RationalApprox.bounds_kappa4}
    In the setting of \cref{lem:boundskappa3}, let $\sqrt[+]{x}$ be an upper square-root function, i.e., $\sqrt{x} \leq \sqrt[+]{x}$ for all real $x \geq 0$ with rational output on rational input. Set $\|x\|_{+} \coloneqq \sqrt[+]{\|x\|^2}$. Set
    \[
        A =  \frac{\langle M P, M(P-Q)\rangle - 2 \epsilon  \|P-Q\| \cdot  (\sqrt{2}+\varepsilon)}{ \big(\| M P\|+\sqrt{2} \varepsilon \big) \cdot \big(\|M(P-Q)\|+2 \sqrt{2} \varepsilon\big)}
    \]
    as well as
    \[
        A_{\Q} =         \frac{\langle M_{\Q} \widetilde{P}, M_{\Q} (\widetilde{P}-\widetilde{Q})\rangle - 10\kappa - 2 \epsilon ( \|\widetilde{P}-\widetilde{Q}\| + 2 \kappa ) \cdot  (\sqrt{2}+\varepsilon)}{ \big(\| M_{\Q} \widetilde{P}\|_{+}+\sqrt{2} \varepsilon + 3\kappa \big) \cdot \big(\|M_{\Q}(\widetilde{P}-\widetilde{Q})\|_{+}+2 \sqrt{2} \varepsilon + 6\kappa\big)}.
    \]
    Assume that $A \geq 0$. Then it holds that $A \geq A_{\Q}$.
\end{corollary}
```

:::proof "lem:boundskappa4"
{uses "lem:boundskappa3"}[]

See polyhedron.without.rupert, Corollary 51.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Corollary 51.
\uses{lem:boundskappa3}
\end{proof}
```

:::theorem "thm:local_rational" (lean := "RationalApprox.LocalTheorem.rational_local") (parent := "rational_local_transfer")
{uses "def:ekspanning"}[]

Let $`\PPP` be a polyhedron with radius $`\rho=1` and $`\widetilde{P}_i` be a $`\kappa`-rational approximation of $`P_i \in \PPP`.
Set $`\widetilde{\PPP} = \{\widetilde{P}_i \text{ for } P_i \in \PPP \}`.
Let $`P_1, P_2, P_3, Q_1, Q_2, Q_3 \in \PPP` be not necessarily distinct and assume that
$`P_1, P_2, P_3` and $`Q_1, Q_2, Q_3` are congruent.
Let $`\epsilon>0` and $`\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \Q \cap [-4,4]`.
Set $`\Xib \coloneqq X_{\Q}(\thetab_1,\phib_1), \Xiib \coloneqq X_{\Q}(\thetab_2,\phib_2)` as well as
$`\Mib \coloneqq M_{\Q}(\thetab_1,\phib_1), \Miib \coloneqq M_{\Q}(\thetab_2,\phib_2)`.
Assume that there exist $`\sigma_P, \sigma_Q \in \{0,1\}` such that

$$`
(-1)^{\sigma_P} \langle \Xib,\widetilde{P}_i\rangle>\sqrt{2}\varepsilon + 3\kappa \quad \text{and} \quad
(-1)^{\sigma_Q} \langle \Xiib , \widetilde{Q}_i\rangle>\sqrt{2}\varepsilon + 3\kappa,
`
$$

for all $`i=1,2,3`.
Moreover, assume that $`\widetilde{P}_1,\widetilde{P}_2,\widetilde{P}_3` are $`\epsilon`-$`\kappa`-spanning for $`(\thetab_1,\phib_1)` and that
$`\widetilde{Q}_1,\widetilde{Q}_2,\widetilde{Q}_3` are $`\epsilon`-$`\kappa`-spanning for $`(\thetab_2,\phib_2)`.
Let $`\sqrt[+]{x}` and $`\sqrt[-]{x}` be upper- and lower-square-root functions, then set
$`\|Z\|_{+} \coloneqq \sqrt[+]{\|Z\|^2}` and $`\|Z\|_{-} \coloneqq \sqrt[-]{\|Z\|^2}` for $`Z \in \R^n`.
Finally, assume that for all $`i = 1,2,3` and any $`\widetilde{Q}_j \in \widetilde{\PPP} \setminus \widetilde{Q}_i` it holds that the rational inequality $`(B^{\Q}_\epsilon)` from the paper is satisfied, for some $`r >0`
such that $`\min_{i=1,2,3}\| \Miib \widetilde{Q}_i \|_{-} > r + \sqrt{2} \epsilon + 3\kappa` and for some $`\delta \in \R`
with

$$`
\delta \geq \max_{i=1,2,3}\left\|R_{\Q}(\alphab) \Mib \widetilde{P}_i-\Miib \widetilde{Q}_i\right\|_{+}/2 + 3\kappa.
`
$$

Then there exists no solution to Rupert's problem $`R(\alpha) M(\theta_1,\phi_1)\PPP \subset  M(\theta_2,\phi_2)\PPP^\circ` with

$$`
(\theta_1, \phi_1, \theta_2, \phi_2, \alpha) \in [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \subseteq \R^5.
`
$$
:::

```tex
\begin{theorem}[Rational Local Theorem]
\label{thm:local_rational}
\leanok
\lean{RationalApprox.LocalTheorem.rational_local}
\uses{def:ekspanning}
    Let $\PPP$ be a polyhedron with radius $\rho=1$ and $\widetilde{P}_i$ be a $\kappa$-rational approximation of $P_i \in \PPP$. Set $\widetilde{\PPP} = \{\widetilde{P}_i \text{ for } P_i \in \PPP \}$. Let $P_1, P_2, P_3, Q_1, Q_2, Q_3 \in \PPP$ be not necessarily distinct and assume that $P_1, P_2, P_3$ and $Q_1, Q_2, Q_3$ are congruent.
    Let $\epsilon>0$ and $\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \Q \cap [-4,4]$.
    Set $\Xib \coloneqq X_{\Q}(\thetab_1,\phib_1), \Xiib \coloneqq X_{\Q}(\thetab_2,\phib_2)$ as well as $\Mib \coloneqq M_{\Q}(\thetab_1,\phib_1), \Miib \coloneqq M_{\Q}(\thetab_2,\phib_2)$.
    Assume that there exist $\sigma_P, \sigma_Q \in \{0,1\}$ such that
    \[
        (-1)^{\sigma_P} \langle \Xib,\widetilde{P}_i\rangle>\sqrt{2}\varepsilon + 3\kappa \quad \text{and} \quad
        (-1)^{\sigma_Q} \langle \Xiib , \widetilde{Q}_i\rangle>\sqrt{2}\varepsilon + 3\kappa, \tag{A$^{\Q}_\epsilon$}
    \]
    for all $i=1,2,3$.
    Moreover, assume that $\widetilde{P}_1,\widetilde{P}_2,\widetilde{P}_3$ are $\epsilon$-$\kappa$-spanning for $(\thetab_1,\phib_1)$ and that $\widetilde{Q}_1,\widetilde{Q}_2,\widetilde{Q}_3$ are $\epsilon$-$\kappa$-spanning for $(\thetab_2,\phib_2)$. Let $\sqrt[+]{x}$ and $\sqrt[-]{x}$ be upper- and lower-square-root functions (bounding $\sqrt{x}$ from above/below for all real $x \geq 0$, with rational output on rational input), then set $\|Z\|_{+} \coloneqq \sqrt[+]{\|Z\|^2}$ and $\|Z\|_{-} \coloneqq \sqrt[-]{\|Z\|^2}$ for $Z \in \R^n$.
    Finally, assume that for all $i = 1,2,3$ and any $\widetilde{Q}_j \in \widetilde{\PPP} \setminus \widetilde{Q}_i$ it holds that
    \[
        \frac{\langle \Miib \widetilde{Q}_i,\Miib (\widetilde{Q}_i-\widetilde{Q}_j)\rangle - 10\kappa - 2 \epsilon ( \|\widetilde{Q}_i-\widetilde{Q}_j\|_{+} + 2 \kappa ) \cdot  (\sqrt{2}+\varepsilon)}{ \big(\|\Miib \widetilde{Q}_i\|_{+}+\sqrt{2} \varepsilon + 3\kappa \big) \cdot \big(\|\Miib(\widetilde{Q}_i-\widetilde{Q}_j)\|_{+}+2 \sqrt{2} \varepsilon + 6\kappa\big)} > \frac{\sqrt{5} \epsilon + \delta}{r}, \tag{B$^{\Q}_\epsilon$}
    \]
    for some $r >0$ such that $\min_{i=1,2,3}\| \Miib \widetilde{Q}_i \|_{-} > r + \sqrt{2} \epsilon + 3\kappa$ and for some $\delta \in \R$ with
    \[
        \delta \geq \max_{i=1,2,3}\left\|R_{\Q}(\alphab) \Mib \widetilde{P}_i-\Miib \widetilde{Q}_i\right\|_{+}/2 + 3\kappa.
    \]
    Then there exists no solution to Rupert's problem $R(\alpha) M(\theta_1,\phi_1)\PPP \subset  M(\theta_2,\phi_2)\PPP^\circ$ with
    \[
        (\theta_1, \phi_1, \theta_2, \phi_2, \alpha) \in [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \subseteq \R^5.
    \]
\end{theorem}
```

:::proof "thm:local_rational"
{uses "thm:local"}[] {uses "lem:boundskappa3"}[] {uses "lem:boundskappa4"}[] {uses "corr:deltakappa"}[] {uses "lem:ekspanningespanning"}[]
:::

```tex
\begin{proof}
\leanok
\uses{thm:local,lem:boundskappa3,lem:boundskappa4,corr:deltakappa,lem:ekspanningespanning},
\end{proof}
```
