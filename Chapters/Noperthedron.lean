/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Commands.Bibliography
import VersoBlueprint.Widget
import VersoBlueprint.MathLint

-- FIXME: This should happen in a special verso code block
import Noperthedron.Basic
import Noperthedron.Bounding
import Noperthedron.PointSym
import Noperthedron.Tightening
import Bibliography

--set_option trace.Elab.info true

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal
open Noperthedron

-- EJGA: Seems like a good idea for hybrid setups
set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option maxHeartbeats 500000

set_option pp.rawOnError true

set_option verso.blueprint.foldProofs true
set_option verso.blueprint.math.lint true

-- set_option trace.Elab.info true

-- No warnings for line length (warning more globally?)
-- Look at ref manual, global options
set_option verso.code.warnLineLength 0

#doc (Manual) "The Noperthedron" =>

:::group "nopert_construction"
Noperthedron construction and core definitions.
:::

:::group "nopert_radius"
Radius and norm control for noperthedron vertices.
:::

:::group "nopert_pointsymmetry"
Pointsymmetry properties of the construction.
:::

:::group "nopert_rupert_tightening"
Rupert-tightening reduction lemmas.
:::

# Definition of the Noperthedron

We define three points $`C_1,C_2,C_3\in \mathbb{Q}^3`.
$$`
    C_1\coloneqq
        \frac{1}{259375205}
        \begin{pmatrix}
        {152024884} \\ 0 \\ {210152163}
        \end{pmatrix},
\qquad
    C_2\coloneqq \frac{1}{10^{10}}
        \begin{pmatrix}
        6632738028 \\ 6106948881 \\ 3980949609
        \end{pmatrix},
`
$$`
    C_3\coloneqq
        \frac{1}{10^{10}}
        \begin{pmatrix}
        8193990033 \\ 5298215096 \\ 1230614493
        \end{pmatrix}.
`

```tex
We define three points $C_1,C_2,C_3\in \mathbb{Q}^3$.
\[
    C_1\coloneqq
        \frac{1}{259375205}
        \begin{pmatrix}
        {152024884} \\ 0 \\ {210152163}
        \end{pmatrix},
\qquad
    C_2\coloneqq \frac{1}{10^{10}}
        \begin{pmatrix}
        6632738028 \\ 6106948881 \\ 3980949609
        \end{pmatrix},
\]
\[
    C_3\coloneqq
        \frac{1}{10^{10}}
        \begin{pmatrix}
        8193990033 \\ 5298215096 \\ 1230614493
        \end{pmatrix}.
\]
```

:::lemma_ "c1_c2_c3_norms" (lean := "Noperthedron.c1_norm_one,Noperthedron.c2_norm_bound,Noperthedron.c3_norm_bound") (parent := "nopert_radius")
$`\| C_1 \| = 1`,
$`{98 \over 100} < \| C_2 \| < {99 \over 100}`, and
$`{98 \over 100} < \| C_3 \| < {99 \over 100}`.
:::

```tex
\begin{lemma}
\label{c1_c2_c3_norms}
\lean{Noperthedron.c1_norm_one, Noperthedron.c2_norm_bound, Noperthedron.c3_norm_bound}
\leanok
$\| C_1 \| = 1$,
${98 \over 100} < \| C_2 \| < {99 \over 100}$, and
${98 \over 100} < \| C_3 \| < {99 \over 100}$.
\end{lemma}
```

:::proof "c1_c2_c3_norms"
Trivial arithmetic.
:::

```tex
\begin{proof}
\leanok
Trivial arithmetic.
\end{proof}
```

Rotations about the $`x, y, z` axes $`R_x,R_y,R_z:`  $`\mathbb{R}\to \mathbb{R}^{3\times 3}`
are defined in the usual way:
$$`
      R_x(\alpha)\coloneqq
        \begin{pmatrix}
            1 & 0 & 0\\
            0 & \cos\alpha & -\sin\alpha\\
            0 & \sin\alpha & \cos\alpha
        \end{pmatrix},
        \hspace{1cm}
        R_y(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & 0 & -\sin\alpha\\
            0 & 1 & 0\\
            \sin\alpha & 0 & \cos\alpha
        \end{pmatrix},
`
$$`
        R_z(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & -\sin\alpha &0\\
            \sin\alpha & \cos\alpha &0\\
            0 & 0 & 1
        \end{pmatrix}.
`

```tex
Rotations about the $x, y, z$ axes $R_x,R_y,R_z:$  $\mathbb{R}\to \mathbb{R}^{3\times 3}$
are defined in the usual way:
    \[
            R_x(\alpha)\coloneqq
        \begin{pmatrix}
            1 & 0 & 0\\
            0 & \cos\alpha & -\sin\alpha\\
            0 & \sin\alpha & \cos\alpha
        \end{pmatrix},
        \hspace{1cm}
        R_y(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & 0 & -\sin\alpha\\
            0 & 1 & 0\\
            \sin\alpha & 0 & \cos\alpha
        \end{pmatrix},
    \]
    \[
        R_z(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & -\sin\alpha &0\\
            \sin\alpha & \cos\alpha &0\\
            0 & 0 & 1
        \end{pmatrix}.
    \]
```

We define a 30-element set $`C_{30}`
$$`
    \mathcal{C}_{30} \coloneqq \left\{(-1)^\ell R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14; \ell=0,1\right\}.
`
of rotations.

```tex
We define a 30-element set $C_{30}$
\[
    \mathcal{C}_{30} \coloneqq \left\{(-1)^\ell R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14; \ell=0,1\right\}.
\]
of rotations.
```

We write $`\mathcal{C}_{30} \cdot P = \{c P \,\text{ for } \, c \in \mathcal{C}_{30}\}` for the orbit of $`P` under the action of $`\mathcal{C}_{30}`.

```tex
We write $\mathcal{C}_{30} \cdot P = \{c P \,\text{ for } \, c \in \mathcal{C}_{30}\}$ for the orbit of $P$ under the action of $\mathcal{C}_{30}$.
```

:::definition "def:noperthedron" (lean := "Noperthedron.exactVertex") (parent := "nopert_construction")
The Noperthedron is the polyhedron given by the vertex set
$$`
\mathcal{C}_{30} \cdot C_1 \cup \mathcal{C}_{30} \cdot C_2 \cup \mathcal{C}_{30} \cdot C_3.
`
:::

```tex
\begin{definition}
\label{def:noperthedron}
\lean{Noperthedron.exactVertex}
\leanok
The Noperthedron is polyhedron given by the vertex set
\[\mathcal{C}_{30} \cdot C_1 \cup \mathcal{C}_{30} \cdot C_2 \cup \mathcal{C}_{30} \cdot C_3\]
\end{definition}
```

:::lemma_ "lemma:nopert_verts_norm_le_one" (lean := "Noperthedron.exactVertex_norm_le_one") (parent := "nopert_radius")
The norm of any vertex in the Noperthedron is no more than 1.
:::

```tex
\begin{lemma}
\label{lemma:nopert_verts_norm_le_one}
\lean{Noperthedron.exactVertex_norm_le_one}
\leanok
The norm of any vertex in the Noperthedron is no more than 1.
\end{lemma}
```

:::proof "lemma:nopert_verts_norm_le_one"
Evident from definitions.
:::

```tex
\begin{proof}
\leanok
Evident from definitions.
\end{proof}
```

:::definition "def:pointsymmetric" (lean := "PointSym") (parent := "nopert_construction")
A set $`S \subseteq \R^3` is _point-symmetric_ if $`x \in S` implies $`-x \in S`.
:::

```tex
\begin{definition}
\label{def:pointsymmetric}
\lean{PointSym}
\leanok
A set $S \subseteq \R^3$ is {\em point-symmetric} if $x \in S$ implies $-x \in S$.
\end{definition}
```

:::lemma_ "lemma:nopert_point_symmetric" (lean := "Noperthedron.exactPoly_point_symmetric") (parent := "nopert_pointsymmetry") (uses := "def:pointsymmetric, def:noperthedron")

The noperthedron is point-symmetric.
:::

```tex
\begin{lemma}
\label{lemma:nopert_point_symmetric}
\lean{Noperthedron.exactPoly_point_symmetric}
\leanok
\uses{def:pointsymmetric, def:noperthedron}
The noperthedron is point-symmetric.
\end{lemma}
```

:::proof "lemma:nopert_point_symmetric"
Follows directly from the definition of the exact vertex set.
:::

```tex
\begin{proof}
\leanok
Follows directly from the definition of the exact vertex set.
\end{proof}
```

# Refined Rupert's property for the Noperthedron

:::lemma_ "lem:symmetries" (lean := "Noperthedron.Tightening.lemma7_1,Noperthedron.Tightening.lemma7_2,Noperthedron.Tightening.lemma7_3") (parent := "nopert_rupert_tightening")

Let $`\PPP = \NOP`, then for all $`\theta, \varphi, \alpha \in \R`, the following three identities hold (as sets):

$$`
\begin{align*}
    M({\theta+2\pi/15,\varphi})\cdot \PPP &=M(\theta, \phi) \cdot \PPP,\\
    R(\alpha+\pi)M(\theta, \phi) \cdot \PPP &=R(\alpha)M(\theta, \phi) \cdot \PPP,\\
    \begin{pmatrix}
        1&0\\
        0&-1
    \end{pmatrix}
    M(\theta, \phi) \cdot \PPP&=
    M({\theta+\pi/15,\pi-\varphi}) \cdot \PPP.
\end{align*}
`
:::

```tex
\begin{lemma} \label{lem:symmetries}
\leanok
\lean{Noperthedron.Tightening.lemma7_1,Noperthedron.Tightening.lemma7_2,Noperthedron.Tightening.lemma7_3}
Let $\PPP = \NOP$, then for all $\theta, \varphi, \alpha \in \R$, the following three identities hold (as sets):
\begin{align*}
    M({\theta+2\pi/15,\varphi})\cdot \PPP &=M(\theta, \phi) \cdot \PPP,\\
    R(\alpha+\pi)M(\theta, \phi) \cdot \PPP &=R(\alpha)M(\theta, \phi) \cdot \PPP,\\
    \begin{pmatrix}
        1&0\\
        0&-1
    \end{pmatrix}
    M(\theta, \phi) \cdot \PPP&=
    M({\theta+\pi/15,\pi-\varphi}) \cdot \PPP.
\end{align*}
\end{lemma}
```

:::proof "lem:symmetries"
See polyhedron.without.rupert, Lemma 7.
:::

```tex
\begin{proof}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 7.
\end{proof}
```

:::corollary "cor:rupert_tightening" (lean := "Noperthedron.Tightening.rupert_tightening") (parent := "nopert_rupert_tightening")

If the noperthedron is Rupert, then there exists a solution with

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
\begin{corollary}
\label{cor:rupert_tightening}
\lean{Noperthedron.Tightening.rupert_tightening}
\leanok
If the noperthedron is Rupert, then there exists a solution with
\begin{align*}
\theta_1,\theta_2&\in[0,2\pi/15] \subset [0,0.42], \\
\varphi_1&\in [0,\pi] \subset [0,3.15],\\
\varphi_2&\in [0,\pi/2] \subset [0,1.58],\\
\alpha &\in [-\pi/2,\pi/2] \subset [-1.58,1.58].
\end{align*}
\end{corollary}
```

:::proof "cor:rupert_tightening" (uses := "lem:symmetries")

See polyhedron.without.rupert, Lemma 8.
:::

```tex
\begin{proof}
\uses{lem:symmetries}
\leanok
See \cite{polyhedron.without.rupert}, Lemma 8.
\end{proof}
```
