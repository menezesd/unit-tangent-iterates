import UnitTangentIterates.MarkedShift
import UnitTangentIterates.PathFromInfimum

/-!
# Extracting marked paths from the phase-quotient infimum

The compatible-marking step of the paper works with the path pseudodistance
modulo a cyclic shift.  This file turns a bound for that infimum into the
concrete phase and normal path needed by the finite-column compactness
construction.  The two infimum extractions cost two copies of an arbitrary
positive slack: one chooses the phase, and one chooses a path at that phase.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath

namespace MarkedShift

/-- A bound in `pathDistShift` yields one phase and one actual normal path.
The additive loss is arbitrarily small and can therefore be chosen summably
in a triangular construction. -/
theorem exists_shift_path_of_pathDistShift_le
    {p q : Data} {B eps : ℝ} (heps : 0 < eps)
    (hne : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (h : pathDistShift p q ≤ B) :
    ∃ b : ℝ, ∃ Gamma : NormalPath p (shiftData b q),
      cost Gamma ≤ B + 2 * eps := by
  have hlt : pathDistShift p q < pathDistShift p q + eps := by
    linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ,
      pathDist p (shiftData b q) < pathDistShift p q + eps := by
    have H := exists_lt_of_ciInf_lt
      (f := fun b : ℝ ↦ pathDist p (shiftData b q)) hlt
    simpa [pathDistShift] using H
  obtain ⟨Gamma, hGamma⟩ :=
    PathMetric.exists_path_of_pathDist_le heps (hne b) hb.le
  refine ⟨b, Gamma, ?_⟩
  linarith

/-- Simultaneous extraction with a caller-chosen positive slack sequence. -/
theorem exists_shift_paths_of_pathDistShift_le
    {Q R : ℕ → Data} {d eps : ℕ → ℝ}
    (hne : ∀ n b, Nonempty (NormalPath (Q n) (shiftData b (R n))))
    (h : ∀ n, pathDistShift (Q n) (R n) ≤ d n)
    (heps : ∀ n, 0 < eps n) :
    ∀ n, ∃ b : ℝ, ∃ Gamma : NormalPath (Q n) (shiftData b (R n)),
      cost Gamma ≤ d n + 2 * eps n := by
  intro n
  exact exists_shift_path_of_pathDistShift_le (heps n) (hne n) (h n)

end MarkedShift
