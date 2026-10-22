/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Macros
import Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

#doc (Manual) "Introduction" =>

Steininger and Yurkevich {citet polyhedron.without.rupert}[] constructed a convex
polyhedron, the *Noperthedron*, and proved that it does not have Rupert's
property: no copy of it can be passed through a hole in another copy. This blueprint
describes a Lean proof of the same theorem that is checked by the Lean kernel alone,
using only the standard axioms.

```tex
Steininger and Yurkevich~\cite{polyhedron.without.rupert} constructed a convex
polyhedron, the \emph{Noperthedron}, and proved that it does not have Rupert's
property: no copy of it can be passed through a hole in another copy. This blueprint
describes a Lean proof of the same theorem that is checked by the Lean kernel alone,
using only the standard axioms.
```

The overall strategy agrees with {citet polyhedron.without.rupert}[]: reduce to purely
rotational passages, use the symmetries of the Noperthedron to shrink the space of
rotation pairs to a bounded box, cover that box by a large tree of sub-boxes, and
exclude each sub-box by exhibiting an inner vertex whose shadow lies outside the outer
shadow. The details differ in several ways.

```tex
The overall strategy agrees with~\cite{polyhedron.without.rupert}: reduce to purely
rotational passages, use the symmetries of the Noperthedron to shrink the space of
rotation pairs to a bounded box, cover that box by a large tree of sub-boxes, and
exclude each sub-box by exhibiting an inner vertex whose shadow lies outside the outer
shadow. The details differ in several ways.
```

- **Rational coordinates.** Rotations are parametrized by Cayley
     coordinates (Chapter {ref "chap:cayley"}[Cayley coordinates]) instead of angles. Every rotation matrix
     in the case analysis is a rational function of the box coordinates, so every leaf
     check is exact polynomial arithmetic. The only irrational numbers are the fixed
     constants $`\cos(2\pi k/15)`, $`\sin(2\pi k/15)` and the vertices
     (Chapter {ref "chap:data"}[Irrational data]).
- **A different reduction.** The symmetry reduction
     (Chapter {ref "chap:reduction"}[The reduction]) puts the outer view in a wedge, picks the relative
     rotation from its orbit under the symmetries by maximizing a score, and covers the
     result by five Cayley charts.
- **No local theorem.** Near the configurations where the inner and outer
     shadows coincide, {citet polyhedron.without.rupert}[] uses a separate local argument.
     Here these configurations are blown up (Section {ref "sec:blowup"}[The blow-up]): the vanishing
     gap factors exactly, and the remaining factor is checked like any other polynomial.
- **Polynomial bounds instead of Lipschitz bounds.** A box is excluded by
     a lower bound of a polynomial on $`[-1,1]^5` (Chapter {ref "chap:polybounds"}[Lower bounds of polynomials]), computed
     from its coefficients or from its Bernstein coefficients.

```tex
\begin{itemize}
\item \textbf{Rational coordinates.} Rotations are parametrized by Cayley
  coordinates (Chapter~\ref{chap:cayley}) instead of angles. Every rotation matrix
  in the case analysis is a rational function of the box coordinates, so every leaf
  check is exact polynomial arithmetic. The only irrational numbers are the fixed
  constants $\cos(2\pi k/15)$, $\sin(2\pi k/15)$ and the vertices
  (Chapter~\ref{chap:data}).
\item \textbf{A different reduction.} The symmetry reduction
  (Chapter~\ref{chap:reduction}) puts the outer view in a wedge, picks the relative
  rotation from its orbit under the symmetries by maximizing a score, and covers the
  result by five Cayley charts.
\item \textbf{No local theorem.} Near the configurations where the inner and outer
  shadows coincide, \cite{polyhedron.without.rupert} uses a separate local argument.
  Here these configurations are blown up (Section~\ref{sec:blowup}): the vanishing
  gap factors exactly, and the remaining factor is checked like any other polynomial.
\item \textbf{Polynomial bounds instead of Lipschitz bounds.} A box is excluded by
  a lower bound of a polynomial on $[-1,1]^5$ (Chapter~\ref{chap:polybounds}), computed
  from its coefficients or from its Bernstein coefficients.
\end{itemize}
```

The case analysis is a tree with $`245{,}484` leaves. It is produced by an untrusted
floating-point search and checked by a Lean function that the kernel evaluates
(Chapter {ref "chap:main"}[The case analysis and the main theorem]).

```tex
The case analysis is a tree with $245{,}484$ leaves. It is produced by an untrusted
floating-point search and checked by a Lean function that the kernel evaluates
(Chapter~\ref{chap:main}).
```
