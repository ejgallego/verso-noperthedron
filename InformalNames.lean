import Noperthedron.Basic
import Noperthedron.PointSym

open scoped Matrix
open Real

namespace Nopert

/-- Blueprint-facing name for the 15-fold rotation orbit used in the prose source. -/
noncomputable def C15 (pt : ℝ³) : Finset ℝ³ :=
  Finset.range 15 |>.image fun (k : ℕ) =>
    RzL (2 * π * (k : ℝ) / 15) pt

end Nopert

/-- Add the antipodal image of every point in a set. -/
def pointsymmetrize {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  S ∪ (-·) '' S

theorem pointsymmetrize_is_pointsym {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    PointSym (pointsymmetrize S) := by
  intro x hx
  rw [pointsymmetrize] at hx ⊢
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact Or.inr ⟨x, hx, rfl⟩
  · apply Or.inl
    rw [← hxy]
    simpa using hy

theorem pointsymmetrize_pres_radius {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x ∈ pointsymmetrize S, ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  intro x hx
  rw [pointsymmetrize] at hx
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact ⟨x, hx, rfl⟩
  · refine ⟨y, hy, ?_⟩
    rw [← hxy]
    simp
