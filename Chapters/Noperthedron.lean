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

```internal
open scoped Matrix
namespace NopertInline
open Real
```

# Definition of the Noperthedron

:::definition "def:noperthedron_main" (parent := "nopert_construction")
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
:::

```lean "def:noperthedron_main"
def C1 : Fin 3 → ℚ := (1/259375205) * ![152024884, 0, 210152163]
def C2 : Fin 3 → ℚ := (1/10^10) * ![6632738028, 6106948881, 3980949609]
def C3 : Fin 3 → ℚ := (1/10^10) * ![8193990033, 5298215096, 1230614493]

noncomputable
def C1R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C1 i)

noncomputable
def C2R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C2 i)

noncomputable
def C3R : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => C3 i)
```

:::lemma_ "c1_c2_c3_norms" (parent := "nopert_radius")
$`\| C_1 \| = 1`,
$`{98 \over 100} < \| C_2 \| < {99 \over 100}`, and
$`{98 \over 100} < \| C_3 \| < {99 \over 100}`.
:::

:::proof "c1_c2_c3_norms"
Trivial arithmetic.
:::

```lean "c1_c2_c3_norms"

-- expose: {NopertInline.c1_norm_one, NopertInline.c2_norm_bound, NopertInline.c3_norm_bound, NopertInline.C15}

theorem c1_norm_one : ‖C1R‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have lez : 0 ≤ ∑ i, ‖C1R i‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg (‖C1R i‖)
  rw [← Real.sq_sqrt lez]
  simp only [Real.norm_eq_abs, sq_abs]
  unfold C1R C1
  simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
  norm_num

theorem c2_norm_bound : ‖C2R‖ ∈ Set.Ioo (98/100) (99/100) := by
  rw [EuclideanSpace.norm_eq]
  constructor
  · refine lt_sqrt_of_sq_lt ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C2R C2
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num
  · refine (sqrt_lt' (by norm_num)).mpr ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C2R C2
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num

theorem c2_norm_le_one : ‖C2R‖ ≤ 1 := by
  grw [c2_norm_bound.2]
  norm_num

theorem c3_norm_bound : ‖C3R‖ ∈ Set.Ioo (98/100) (99/100) := by
  rw [EuclideanSpace.norm_eq]
  constructor
  · sorry
  · refine (sqrt_lt' (by norm_num)).mpr ?_
    simp only [Real.norm_eq_abs, sq_abs]
    unfold C3R C3
    simp only [Fin.sum_univ_three, Pi.mul_apply, Matrix.cons_val]
    norm_num

-- deps for c3_norm_bound:
--   { EuclideanSpace.norm_eq, lt_sqrt_of_sq_lt, Real.norm_eq_abs, C3R, C3,  }
-- deps we know: { }

theorem c3_norm_le_one : ‖C3R‖ ≤ 1 := by
  grw [c3_norm_bound.2]
  norm_num

/-- This is half of the C30 defined in \[SY25\]. In order
to see that this is pointsymmetric, it's convenient to
do explicit pointsymmetrization later. -/
noncomputable
def C15 (pt : ℝ³) : Finset ℝ³ :=
  Finset.range 15 |> .image fun (k : ℕ)  =>
    RzL (2 * π * (k : ℝ) / 15) pt

lemma C15_nonempty (pt : ℝ³) : (C15 pt).Nonempty := by
  use (RzL 0 pt)
  have z : 0 ∈ Finset.range 15 := Finset.insert_eq_self.mp rfl
  simp only [C15, Finset.mem_image, Finset.mem_range]
  use 0
  simp only [Nat.ofNat_pos, CharP.cast_eq_zero, mul_zero, zero_div, and_self]

lemma C15_pres_norm (pt v : ℝ³) (hv : v ∈ C15 pt) : ‖v‖ = ‖pt‖ := by
  simp only [C15, Finset.mem_image, Finset.mem_range] at hv
  obtain ⟨a, ⟨ha, ha'⟩⟩ := hv
  rw [← ha', Bounding.Rz_preserves_norm _]

end NopertInline
```

:::lemma_ "lem:radius_noperthedron_one" (parent := "nopert_radius")
The radius of the Noperthedron is one.
:::

:::proof "lem:radius_noperthedron_one"
By {uses "c1_c2_c3_norms"}[], {uses "thm:pointsymmetrize_pres_radius"}[],
{uses "thm:polyhedron_radius_def"}[], and {uses "lemma:half_nopert_verts_norm_le_one"}[].
:::

```lean "lem:radius_noperthedron_one"
namespace NopertInline

/--
Half of the vertices of the noperthedron
-/
noncomputable
def halfNopertVerts : Finset ℝ³ :=
    Nopert.C15 Nopert.C1R ∪
    Nopert.C15 Nopert.C2R ∪
    Nopert.C15 Nopert.C3R

lemma half_nopert_verts_nonempty : halfNopertVerts.Nonempty := by
  apply Finset.Nonempty.inl
  apply Finset.Nonempty.inl
  apply Nopert.C15_nonempty

noncomputable
def halfNopertNorms : Finset ℝ :=
  halfNopertVerts.image (‖·‖)

lemma half_nopert_norms_nonempty : halfNopertNorms.Nonempty := by
  simp only [halfNopertNorms, Finset.image_nonempty]
  exact half_nopert_verts_nonempty

lemma half_nopert_verts_norm_le_one : ∀ v ∈ halfNopertVerts, ‖v‖ ≤ 1 := by
  intro v hv
  simp only [halfNopertVerts, Finset.union_assoc, Finset.mem_union] at hv
  rcases hv with h | h | h
  · rw [show ‖v‖ = ‖Nopert.C1R‖ from Nopert.C15_pres_norm Nopert.C1R v h, Nopert.c1_norm_one]
  · rw [show ‖v‖ = ‖Nopert.C2R‖ from Nopert.C15_pres_norm Nopert.C2R v h]
    exact Nopert.c2_norm_le_one
  · rw [show ‖v‖ = ‖Nopert.C3R‖ from Nopert.C15_pres_norm Nopert.C3R v h]
    exact Nopert.c3_norm_le_one

@[simp]
noncomputable
def pointsymmetrize (vs : Finset ℝ³) : Finset ℝ³ := vs ∪ vs.image (-·)

lemma pointsymmetrize_mem (vs : Finset ℝ³) (x : ℝ³)  :
    (x ∈ pointsymmetrize vs) ↔ (x ∈ vs ∨ -x ∈ vs) := by
  constructor
  · intro hx
    simp_all only [pointsymmetrize]
    let z :=  Finset.mem_union.mp hx
    simp only [Finset.mem_image] at z
    match z with
    | .inl h => left; assumption
    | .inr ⟨y, ⟨hy, hy'⟩⟩  => rw [← hy']; right; simpa
  · intro hq
    simp only [pointsymmetrize, Finset.mem_union, Finset.mem_image]
    match hq with
    | .inl h => left; exact h
    | .inr h => right; use -x; simpa

noncomputable
def nopertVerts : Finset ℝ³ :=
  pointsymmetrize halfNopertVerts

/--
The noperthedron, given as a set of vertices.
-/
noncomputable
def nopertVertSet : Set ℝ³ := nopertVerts

lemma nopert_verts_nonempty : nopertVerts.Nonempty := by
  simp only [nopertVerts]
  apply Finset.Nonempty.inl
  apply half_nopert_verts_nonempty

def half_nopert_verts_nontriv : ∀ v ∈ halfNopertVerts, 0 < ‖v‖ := by
  intro v hv
  simp_all only [halfNopertVerts, Finset.union_assoc, Finset.mem_union]
  rcases hv with hv | hv | hv
  all_goals rw [Nopert.C15_pres_norm _ _ hv]
  · exact Nopert.c1_norm_one ▸ Real.zero_lt_one
  · linarith [Nopert.c2_norm_bound.1]
  · linarith [Nopert.c3_norm_bound.1]

def nopert_verts_nontriv : ∀ v ∈ nopertVerts, 0 < ‖v‖ := by
  simp only [nopertVerts, pointsymmetrize, Finset.mem_union, Finset.mem_image]
  intro v hv
  rcases hv with hv | ⟨a, ha₁, ha₂⟩
  · exact half_nopert_verts_nontriv v hv
  · rw [← ha₂]; simp only [norm_neg]; exact half_nopert_verts_nontriv a ha₁

noncomputable
def nopert : Shape where
  vertices := nopertVerts

lemma pointsymmetrize_is_pointsym (vs : Finset ℝ³) :
    PointSym (pointsymmetrize vs : Set ℝ³) := by
  intro a ha
  simp only [SetLike.mem_coe]
  have z :  a ∈ vs ∨ -a ∈ vs :=  pointsymmetrize_mem vs a |>.mp ha
  have z' : -a ∈ vs ∨ -(-a) ∈ vs := cast (by rw [or_comm, neg_neg]) z
  exact pointsymmetrize_mem vs (-a) |>.mpr z'

theorem nopert_verts_pointsym : PointSym nopertVertSet :=
  pointsymmetrize_is_pointsym halfNopertVerts

/--
The noperthedron is pointsymmetric.
-/
theorem nopert_point_symmetric : PointSym nopert.hull := by
  exact hull_preserves_pointsym nopert_verts_pointsym

/--
The point C1R is in the half-noperthedron
-/
lemma c1r_in_half_nopert_verts : Nopert.C1R ∈ halfNopertVerts := by
    simp only [halfNopertVerts]
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simp only [Nopert.C15, Finset.mem_image, Finset.mem_range]
    use 0
    rw [show RzL = ⇑RzC by rfl]
    simp

/--
The radius of the half-noperthedron is 1.
-/
theorem half_nopert_radius_one : polyhedronRadius halfNopertVerts half_nopert_verts_nonempty = 1 := by
  apply polyhedron_radius_iff halfNopertVerts half_nopert_verts_nonempty |>.mpr
  exact ⟨Exists.intro Nopert.C1R ⟨c1r_in_half_nopert_verts, Nopert.c1_norm_one⟩, half_nopert_verts_norm_le_one⟩

/--
Pointsymmetrization preserves the radius of any set
-/
theorem pointsymmetrize_pres_radius {vs : Finset ℝ³} (vsne : vs.Nonempty) :
    polyhedronRadius (pointsymmetrize vs) (by simpa) = polyhedronRadius vs vsne := by
  let r := polyhedronRadius vs vsne
  let r' := polyhedronRadius (pointsymmetrize vs) (by simpa)
  have start : (∃ v ∈ vs, ‖v‖ = r) ∧ ∀ v ∈ vs, ‖v‖ ≤ r :=
    polyhedron_radius_iff vs vsne |>.mp rfl
  let ⟨ ⟨ v, v_in_vs,  v_norm_r⟩ , rest_le_r⟩ := start
  suffices finish : (∃ v ∈ (pointsymmetrize vs), ‖v‖ = r) ∧ ∀ v ∈ (pointsymmetrize vs), ‖v‖ ≤ r by
    exact polyhedron_radius_iff (pointsymmetrize vs) (by simpa) |>.mpr finish
  constructor
  · use v;
    refine ⟨?_, v_norm_r⟩
    simp only [pointsymmetrize]; apply Finset.mem_union_left; exact v_in_vs
  · intro v hv
    rw [pointsymmetrize_mem] at hv
    match hv with
    | .inl v_in_vs => apply rest_le_r; assumption
    | .inr mv_in_vs =>
      specialize rest_le_r (-v) mv_in_vs
      rw [norm_neg] at rest_le_r
      exact rest_le_r

/--
The radius of the noperthedron is 1.
-/
theorem Nopert.noperthedron_radius_one : polyhedronRadius nopertVerts nopert_verts_nonempty = 1 := by
  simp only [nopertVerts, pointsymmetrize_pres_radius half_nopert_verts_nonempty]
  exact half_nopert_radius_one

end NopertInline
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

Where Steininger and Yurkevich define a 30-element set $`C_{30}`:

 $$`
    \mathcal{C}_{30} \coloneqq \left\{(-1)^\ell R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14; \ell=0,1\right\}.
`
of rotations, we instead define

:::definition "def:C15" (lean := "Nopert.C15") (parent := "nopert_construction")
$$`
    \mathcal{C}_{15} \coloneqq \left\{ R_z\left(\frac{2\pi k}{15}\right) \colon k=0,\dots,14 \right\}.
`
:::

without point-symmetricness "baked in" as it is in $`C_{30}`. It's more convenient for the formalization to apply $`C_{15}` to the points $`C_1, C_2, C_3`, and then point-symmetrize that set afterwards.

:::definition "def:pointsymmetric" (lean := "PointSym") (parent := "nopert_construction")
A set $`S \subseteq \R^3` is _point-symmetric_ if $`x \in S` implies $`-x \in S`.
:::

:::definition "def:pointsymmetrize" (lean := "pointsymmetrize") (parent := "nopert_construction")

The _pointsymmetrization_ of a collection of vertices $`v_1, \ldots, v_n \in \R^3`
is $`v_1, \ldots, v_n, -v_1, \ldots, -v_n`.
:::

We write $`\mathcal{C}_{15} \cdot P = \{c P \,\text{ for } \, c \in \mathcal{C}_{15}\}` for the orbit of $`P` under the action of $`\mathcal{C}_{15}`.

:::definition "def:noperthedron" (lean := "halfNopertVerts, nopertVerts, nopert") (parent := "nopert_construction")

Using {uses "def:C15"}[].

The Noperthedron is the polyhedron given by the vertex set that is the
{uses "def:pointsymmetrize"}[pointsymmetrization] of
$$`
\mathcal{C}_{15} \cdot C_1 \cup \mathcal{C}_{15} \cdot C_2 \cup \mathcal{C}_{15} \cdot C_3
`
:::

:::lemma_ "lemma:half_nopert_verts_norm_le_one" (lean := "half_nopert_verts_norm_le_one") (parent := "nopert_radius")
The norm of any vertex in the prepointsymmetrized version of the Noperthedron is no more than 1.
:::

:::proof "lemma:half_nopert_verts_norm_le_one" (leanok := true)
Evident from definitions.
:::

:::lemma_ "lemma:pointsymmetrization_is_pointsym" (lean := "pointsymmetrize_is_pointsym") (parent := "nopert_pointsymmetry")
The pointsymmetrization of any set is point-symmetric.
:::

:::proof "lemma:pointsymmetrization_is_pointsym" (leanok := true)
Evident from definitions.
:::

:::lemma_ "lemma:nopert_point_symmetric" (lean := "nopert_point_symmetric") (parent := "nopert_pointsymmetry")
The {uses "def:noperthedron"}[noperthedron] is {uses "def:pointsymmetric"}[point-symmetric].
:::

:::proof "lemma:nopert_point_symmetric" (leanok := true)
Follows from {uses "lemma:pointsymmetrization_is_pointsym"}[]
:::

# Refined Rupert's property for the Noperthedron

:::lemma_ "lem:symmetries" (lean := "Tightening.lemma7_1,Tightening.lemma7_2,Tightening.lemma7_3") (parent := "nopert_rupert_tightening")

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

:::proof "lem:symmetries" (leanok := true)
See {citet polyhedron.without.rupert (kind := lemma) (index := 7)}[].
:::

:::corollary "cor:rupert_tightening" (lean := "Tightening.rupert_tightening") (parent := "nopert_rupert_tightening")

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

:::proof "cor:rupert_tightening" (leanok := true)
Using {uses "lem:symmetries"}[].

See {citep polyhedron.without.rupert (kind := lemma) (index := 8)}[].
:::
