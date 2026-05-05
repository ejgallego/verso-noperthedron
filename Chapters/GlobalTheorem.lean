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
open Noperthedron

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

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

```tex
\begin{lemma} \label{lem:hullscalarprod}
\leanok
\lean{GlobalTheorem.hull_scalar_prod}
Suppose $V = V_1, \ldots, V_m \subseteq \R^n$ be a finite sequence of points. Suppose $\hull V$ is its convex hull.
Let $S \in \hull V$ and $w \in \R^n$ be given. then
    \[
        \langle S ,w \rangle \leq \max_{i} \langle V_i ,w\rangle
    \]
\end{lemma}
```

:::proof "lem:hullscalarprod"
This is a mild generalization of {citet polyhedron.without.rupert (kind := lemma) (index := 18)}[].

Since $`S \in \hull V`, we have
$`S = \sum_{j=1}^m \lambda_j V_j`
for some $`\lambda_1,\ldots,\lambda_m \in [0,1]` with
$`1 = \sum_{j=1}^m \lambda_j`.
Therefore

$$`
\langle S ,w \rangle = \left\langle  \sum_{j=1}^m \lambda_j V_j ,w \right\rangle
=  \sum_{j=1}^m \lambda_j \left\langle   V_j ,w \right\rangle
\le   \sum_{j=1}^m \lambda_j \max_{i} \langle V_i ,w\rangle
`
$$`
=  \max_{i} \langle V_i ,w\rangle \sum_{j=1}^m \lambda_j
=  \max_{i} \langle V_i ,w\rangle
`
$$

as required.
:::

```tex
\begin{proof}
\leanok
This is a mild generalization of \cite{polyhedron.without.rupert}, Lemma 18.

Since $S \in \hull V$, we have
\[ S = \sum_{j=1}^m \lambda_j V_j \]
for some $\lambda_1,\ldots,\lambda_m \in [0,1]$ with
\[ 1 = \sum_{j=1}^m \lambda_j  \]
Therefore
\[
\langle S ,w \rangle = \left\langle  \sum_{j=1}^m \lambda_j V_j ,w \right\rangle
=  \sum_{j=1}^m \lambda_j \left\langle   V_j ,w \right\rangle
\le   \sum_{j=1}^m \lambda_j \max_{i} \langle V_i ,w\rangle
\]
\[
=  \max_{i} \langle V_i ,w\rangle \sum_{j=1}^m \lambda_j
=  \max_{i} \langle V_i ,w\rangle
\]
as required.
\end{proof}
```

:::lemma_ "lem:leq1" (lean := "GlobalTheorem.rotation_partials_bounded") (parent := "global_derivative_bounds")
Let $`S \in \mathbb{R}^3` and $`w \in \mathbb{R}^2` be unit vectors, and set
$`f(x_1,x_2,x_3) = \langle R(x_3) M(x_1,x_2)S,w \rangle`.
Then for all $`x_1,x_2,x_3 \in \mathbb{R}` and any $`i,j \in \{1,2,3\}` it holds that

$$`
\left|\frac{\partial^2 f}{\partial x_i \partial x_j}(x_1,x_2,x_3)\right|\leq 1.
`
:::

```tex
\begin{lemma} \label{lem:leq1}
\lean{GlobalTheorem.rotation_partials_bounded}
\leanok
    Let $S \in \R^3$ and $w \in \R^2$ be unit vectors and set $f(x_1,x_2,x_3) = \langle R(x_3) M(x_1,x_2)S,w \rangle$. Then for all $x_1,x_2,x_3 \in \R$ and any $i,j \in \{1,2,3\}$ it holds that
    \[
        \left|\frac{\dd^2 f}{\dd x_i \dd x_j}(x_1,x_2,x_3)\right|\leq 1.
    \]
\end{lemma}
```

:::proof "lem:leq1"
See polyhedron.without.rupert, Lemma 19.
:::

```tex
\begin{proof}\leanok
See \cite{polyhedron.without.rupert}, Lemma 19.
\end{proof}
```

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

```tex
\begin{lemma} \label{lem:n2}
\lean{GlobalTheorem.bounded_partials_control_difference}
\leanok
    Let $f:\R^n\to \R$ be a $C^2$-function and $x_1,\dots,x_n,y_1,\dots,y_n \in \R$ such that $|x_1-y_1|,\dots,|x_n-y_n|\leq \varepsilon$.
    If
    \(
        \left|\partial_{x_i}\partial_{x_j}f(v)\right| \leq 1
    \)
    for all $i,j \in \{1,\dots,n\}$ and all $v \in \R^n$, then
    \[
    |f(x_1,\dots,x_n)-f(y_1,\dots,y_n)|\leq \varepsilon \sum_{i=1}^n |\partial_{x_i} f(x_1,\dots,x_n)| + \frac{n^2}{2}\varepsilon^2.
    \]
\end{lemma}
```

:::proof "lem:n2"
See polyhedron.without.rupert, Lemma 20.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 20.
\end{proof}
```

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

```tex
\begin{lemma}
\label{lem:rotation_derivatives}
\leanok
\lean{GlobalTheorem.rotation_partials_exist, GlobalTheorem.rotation_partials_exist_outer,
 GlobalTheorem.partials_helper0, GlobalTheorem.partials_helper1, GlobalTheorem.partials_helper2,
 GlobalTheorem.partials_helper3, GlobalTheorem.partials_helper4}
The partial derivatives of all relevant rotations, projections, and inner products
used in the Global Theorem are as expected.
Specifically:
\begin{itemize}
\item \[  f^\alpha(\theta,\phi,\alpha) = \langle R'(\alpha) M(\theta, \phi) S, w \rangle \]
\item \[  f^\theta(\theta,\phi,\alpha) = \langle R(\alpha) M^\theta(\theta, \phi) S, w \rangle \]
\item \[  f^\phi(\theta,\phi,\alpha) = \langle R(\alpha) M^\phi(\theta, \phi) S, w \rangle \]
\item \[  g^\theta(\theta,\phi) = \langle  M^\theta(\theta, \phi) P, w \rangle \]
\item \[  g^\phi(\theta,\phi) = \langle  M^\phi(\theta, \phi) P, w \rangle \]
\end{itemize}
where $f(\theta,\phi,\alpha) =  \langle R(\alpha) M(\theta,\phi) S / \|S\|, w\rangle $
and $g(\theta,\phi) =  \langle M(\theta,\phi) P / \|P\|, w\rangle $.
\end{lemma}
```

:::proof "lem:rotation_derivatives"
By basic properties of derivatives.
:::

```tex
\begin{proof}\leanok
By basic properties of derivatives.
\end{proof}
```

:::theorem "thm:global" (lean := "GlobalTheorem.global_theorem") (parent := "global_main")
Let $`\PPP` be a pointsymmetric convex polyhedron with radius $`\rho =1` and let $`S \in \PPP`.
Further let $`\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \R` and let $`w\in\R^2` be a unit vector.
Denote $`\Mib \coloneqq M(\thetab_1, \phib_1)`, $`\Miib \coloneqq M(\thetab_2, \phib_2)` as well as
$`\Mib^{\theta} \coloneqq M^\theta(\thetab_1, \phib_1)`, $`\Mib^{\phi} \coloneqq M^\phi(\thetab_1, \phib_1)`
and analogously for $`\Miib^{\theta}, \Miib^{\phi}`.
Finally set

$$`
\begin{align*}
G& \coloneqq \langle R(\alphab) \Mib S,w \rangle - \epsilon\cdot\big(|\langle R'(\alphab)  \Mib S,w \rangle|+|\langle R(\alphab) \Mib^\theta S,w \rangle|+|\langle R(\alphab) \Mib^\phi S,w \rangle|\big)- 9\epsilon^2/2,\\
H_P & \coloneqq \langle \Miib P,w \rangle + \epsilon\cdot\big(|\langle \Miib^\theta P,w \rangle|+|\langle  \Miib^\varphi P,w \rangle|\big) + 2\epsilon^2, \quad \text{ for } P \in \PPP.
\end{align*}
`
$$

If $`G>\max_{P\in \PPP} H_P` then there does not exist a solution to Rupert's condition with

$$`
(\theta_1,\varphi_1,\theta_2,\varphi_2,\alpha) \in U \coloneqq [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \subseteq \R^5.
`
:::

```tex
\begin{theorem}[Global Theorem] \label{thm:global}
\lean{GlobalTheorem.global_theorem}
\leanok
    Let $\PPP$ be a pointsymmetric convex polyhedron with radius $\rho =1$ and let $S \in \PPP$. Further let $\thetab_1,\phib_1,\thetab_2,\phib_2,\alphab \in \R$ and let $w\in\R^2$ be a unit vector. Denote $\Mib \coloneqq M(\thetab_1, \phib_1)$, $ \Miib \coloneqq M(\thetab_2, \phib_2)$ as well as $\Mib^{\theta} \coloneqq M^\theta(\thetab_1, \phib_1)$, $\Mib^{\phi} \coloneqq M^\phi(\thetab_1, \phib_1)$ and analogously for $\Miib^{\theta}, \Miib^{\phi}$. Finally set
    \begin{align*}
        G& \coloneqq \langle R(\alphab) \Mib S,w \rangle - \epsilon\cdot\big(|\langle R'(\alphab)  \Mib S,w \rangle|+|\langle R(\alphab) \Mib^\theta S,w \rangle|+|\langle R(\alphab) \Mib^\phi S,w \rangle|\big)- 9\epsilon^2/2,\\
        H_P & \coloneqq \langle \Miib P,w \rangle + \epsilon\cdot\big(|\langle \Miib^\theta P,w \rangle|+|\langle  \Miib^\varphi P,w \rangle|\big) + 2\epsilon^2, \quad \text{ for } P \in \PPP.
    \end{align*}
    If $G>\max_{P\in \PPP} H_P$ then there does not exist a solution to Rupert's condition with
    $$(\theta_1,\varphi_1,\theta_2,\varphi_2,\alpha) \in U \coloneqq [\thetab_1\pm\epsilon,\phib_1\pm\epsilon,\thetab_2\pm\epsilon,\phib_2\pm\epsilon,\alphab\pm\epsilon] \subseteq \R^5.$$
\end{theorem}
```

:::proof "thm:global"
Using {uses "lem:hullscalarprod"}[], {uses "lem:leq1"}[], {uses "lem:n2"}[], and {uses "lem:rotation_derivatives"}[].
See polyhedron.without.rupert, Section 4.2.
:::

```tex
\begin{proof}
\leanok
\uses{lem:hullscalarprod,lem:leq1,lem:n2,lem:rotation_derivatives}
See \cite{polyhedron.without.rupert}, Section~{4.2}.
\end{proof}
```
