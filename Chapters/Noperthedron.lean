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

#doc (Manual) "The Noperthedron" =>

%%%
tag := "chap:noperthedron"
%%%

# Definition of the Noperthedron

We define three points $`C_1,C_2,C_3\in \mathbb{Q}^3`.

```tex
We define three points $C_1,C_2,C_3\in \mathbb{Q}^3$.
```

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

```tex
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
```

$$`
C_3\coloneqq
        \frac{1}{10^{10}}
        \begin{pmatrix}
        8193990033 \\ 5298215096 \\ 1230614493
        \end{pmatrix}.
`

```tex
\[
    C_3\coloneqq
        \frac{1}{10^{10}}
        \begin{pmatrix}
        8193990033 \\ 5298215096 \\ 1230614493
        \end{pmatrix}.
\]
```

:::lemma_ "c1_c2_c3_norms" (lean := "Noperthedron.c1_norm_one, Noperthedron.c2_norm_bound, Noperthedron.c3_norm_bound")
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

```tex
Rotations about the $x, y, z$ axes $R_x,R_y,R_z:$  $\mathbb{R}\to \mathbb{R}^{3\times 3}$
are defined in the usual way:
```

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

```tex
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
```

$$`
R_z(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & -\sin\alpha &0\\
            \sin\alpha & \cos\alpha &0\\
            0 & 0 & 1
        \end{pmatrix}.
`

```tex
\[
        R_z(\alpha)\coloneqq
        \begin{pmatrix}
            \cos\alpha & -\sin\alpha &0\\
            \sin\alpha & \cos\alpha &0\\
            0 & 0 & 1
        \end{pmatrix}.
    \]
```

We define a 30-element set $`\mathcal{C}_{30}`

```tex
We define a 30-element set $\mathcal{C}_{30}$
```

$$`
\mathcal{C}_{30} \coloneqq \left\{(-1)^\ell R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14; \ell=0,1\right\}.
`

```tex
\[
    \mathcal{C}_{30} \coloneqq \left\{(-1)^\ell R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14; \ell=0,1\right\}.
\]
```

of rotations.

```tex
of rotations.
```

We write $`\mathcal{C}_{30} \cdot P = \{c P \,\text{ for } \, c \in \mathcal{C}_{30}\}` for the orbit of $`P` under the action of $`\mathcal{C}_{30}`.

```tex
We write $\mathcal{C}_{30} \cdot P = \{c P \,\text{ for } \, c \in \mathcal{C}_{30}\}$ for the orbit of $P$ under the action of $\mathcal{C}_{30}$.
```

:::definition "def:noperthedron" (lean := "Noperthedron.exactVertex")
The Noperthedron $`\NOP` is the convex polyhedron given by the vertex set

$$`
\mathcal{C}_{30} \cdot C_1 \cup \mathcal{C}_{30} \cdot C_2 \cup \mathcal{C}_{30} \cdot C_3
`
:::

```tex
\begin{definition}
\label{def:noperthedron}
\lean{Noperthedron.exactVertex}
\leanok
The Noperthedron $\NOP$ is the convex polyhedron given by the vertex set
\[\mathcal{C}_{30} \cdot C_1 \cup \mathcal{C}_{30} \cdot C_2 \cup \mathcal{C}_{30} \cdot C_3\]
\end{definition}
```

:::lemma_ "lemma:nopert_verts_norm_le_one" (lean := "Noperthedron.exactVertex_norm_le_one")
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

:::definition "def:pointsymmetric" (lean := "PointSym")
A set $`S \subseteq \R^3` is *point-symmetric* if $`x \in S` implies $`-x \in S`.
:::

```tex
\begin{definition}
\label{def:pointsymmetric}
\lean{PointSym}
\leanok
A set $S \subseteq \R^3$ is {\em point-symmetric} if $x \in S$ implies $-x \in S$.
\end{definition}
```

:::lemma_ "lemma:nopert_point_symmetric" (lean := "Noperthedron.exactPoly_point_symmetric") (uses := "def:pointsymmetric, def:noperthedron")
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
The set $`\mathcal{C}_{30}` contains $`-\id`.
:::

```tex
\begin{proof}
\leanok
The set $\mathcal{C}_{30}$ contains $-\id$.
\end{proof}
```

:::lemma_ "lemma:nopert_interior" (lean := "Noperthedron.interior_exactVerts_hull_nonempty") (uses := "def:noperthedron")
The Noperthedron has nonempty interior.
:::

```tex
\begin{lemma}
\label{lemma:nopert_interior}
\lean{Noperthedron.interior_exactVerts_hull_nonempty}
\leanok
\uses{def:noperthedron}
The Noperthedron has nonempty interior.
\end{lemma}
```

:::proof "lemma:nopert_interior"
Four of its vertices are affinely independent.
:::

```tex
\begin{proof}
\leanok
Four of its vertices are affinely independent.
\end{proof}
```
