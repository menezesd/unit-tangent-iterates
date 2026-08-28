import UnitTangentIterates.PathMetric

/-!
# From `pathDist` bounds to actual paths

The development's defect estimates are stated for `pathDist` — an infimum over
normal paths — while the shadowing schemes consume the existential form
`∃ Λ, cost Λ ≤ dₙ`.  This file is the step between them.

`exists_path_of_pathDist_le` : a bound `pathDist p q ≤ B` produces, for every
margin `ε > 0`, a normal path of cost at most `B + ε`.  The margin cannot be
dispensed with — the infimum need not be attained — but it costs nothing, since
`exists_paths_of_pathDist_le` lets it be chosen as a summable sequence, so the
resulting defects stay summable and the shadowing radius moves by an arbitrarily
small amount.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace

namespace PathMetric

open NormalPath

/-- **From an infimum bound to an actual path.**  `pathDist` is an infimum over
normal paths, so a bound on it produces, for every margin `ε > 0`, a path whose
cost is within `ε`.  This is the step between the `pathDist` estimates the
development proves and the `∃ Λ, cost Λ ≤ dₙ` form the shadowing schemes
consume. -/
theorem exists_path_of_pathDist_le {p q : Data} {B eps : ℝ} (heps : 0 < eps)
    (hne : Nonempty (NormalPath p q)) (h : pathDist p q ≤ B) :
    ∃ Γ : NormalPath p q, cost Γ ≤ B + eps := by
  have hS : (costSet p q).Nonempty := ⟨cost hne.some, ⟨hne.some, rfl⟩⟩
  have hlt : sInf (costSet p q) < B + eps := by
    have := h
    rw [pathDist] at this
    linarith
  obtain ⟨c, hcmem, hclt⟩ := exists_lt_of_csInf_lt hS hlt
  obtain ⟨Γ, hΓ⟩ := hcmem
  exact ⟨Γ, by rw [hΓ]; linarith⟩

/-- The same with the margin chosen as a summable sequence, so that the
resulting defects stay summable. -/
theorem exists_paths_of_pathDist_le {Q : ℕ → Data} {R : ℕ → Data} {d : ℕ → ℝ}
    (hne : ∀ n, Nonempty (NormalPath (Q n) (R n)))
    (h : ∀ n, pathDist (Q n) (R n) ≤ d n) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n) :
    ∀ n, ∃ Γ : NormalPath (Q n) (R n), cost Γ ≤ d n + eps n := fun n =>
  exists_path_of_pathDist_le (heps n) (hne n) (h n)

end PathMetric
