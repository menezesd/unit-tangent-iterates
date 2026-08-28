import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite constant majors for diagonal histories -/

noncomputable section

open scoped BigOperators

namespace FiniteDiagonalSegmentMajor

/-- A depth-`k` forward history at one fixed diagonal pays the same local
analytic error at each of its `k+1` nodes and nothing outside the history. -/
def segmentMajor (eps : ℝ) (k j : ℕ) : ℝ :=
  if j ≤ k then eps else 0

theorem segmentMajor_nonnegative {eps : ℝ} (heps : 0 ≤ eps) (k j : ℕ) :
    0 ≤ segmentMajor eps k j := by
  simp only [segmentMajor]
  split <;> positivity

theorem segmentMajor_summable (eps : ℝ) (k : ℕ) :
    Summable (segmentMajor eps k) := by
  apply summable_of_finite_support
  apply (Set.finite_Iic k).subset
  intro j hj
  by_contra hle
  apply hj
  simp [segmentMajor, Nat.not_le.mp hle]

theorem tsum_segmentMajor (eps : ℝ) (k : ℕ) :
    (∑' j, segmentMajor eps k j) = (k + 1 : ℕ) * eps := by
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · calc
      (∑ x ∈ Finset.range (k + 1), segmentMajor eps k x) =
          ∑ _x ∈ Finset.range (k + 1), eps := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [segmentMajor, Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)]
      _ = (k + 1 : ℕ) * eps := by simp
  · intro j hj
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hj
    simp [segmentMajor, Nat.not_le.mpr hj]

theorem segmentMajor_tsum_le {eps E : ℝ} {k : ℕ}
    (h : (k + 1 : ℕ) * eps ≤ E) :
    (∑' j, segmentMajor eps k j) ≤ E := by
  simpa [tsum_segmentMajor] using h

theorem segmentMajor_eq {eps : ℝ} {k j : ℕ} (hj : j ≤ k) :
    segmentMajor eps k j = eps := by
  simp [segmentMajor, hj]

theorem adjacent_le {eps : ℝ} (heps : 2 * eps ≤ 1 / 4)
    {k j : ℕ} (hj : j < k) :
    segmentMajor eps k j + segmentMajor eps k (j + 1) ≤ 1 / 4 := by
  rw [segmentMajor_eq (Nat.le_of_lt hj),
    segmentMajor_eq (Nat.succ_le_of_lt hj)]
  linarith

end FiniteDiagonalSegmentMajor
