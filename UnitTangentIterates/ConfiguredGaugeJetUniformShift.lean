import UnitTangentIterates.ConfiguredGaugeJetDistortion
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget
import UnitTangentIterates.ConstructedRowDefectLargeSeparation

/-!
# One configured shift makes every gauge marking near the identity

Because the gauge error depends only on `n+k`, an eventual estimate for row
zero becomes a uniform estimate for all rows and depths after one common
separation shift.
-/

noncomputable section

namespace ConfiguredGaugeJetUniformShift

open ConfiguredGaugeJetDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData

theorem eps_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (Cjet : ℝ)
    (N n k : ℕ) :
    eps (shift D N) Cjet n k = eps D Cjet 0 (N + n + k) := by
  simp [eps, ConstructedRowDefectLargeSeparation.rowDefect_shift,
    Nat.add_assoc]

theorem exists_shift_eps_le_half
    (D : ConstructedConfiguredSequenceWeighted.Data) (Cjet : ℝ) :
    ∃ N, ∀ n k, eps (shift D N) Cjet n k ≤ 1 / 2 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_eps_le_half D (Cjet := Cjet) 0)
  refine ⟨N, ?_⟩
  intro n k
  have h := hN (N + (n + k)) (Nat.le_add_right N (n + k))
  rw [eps_shift]
  simpa [Nat.add_assoc] using h

/-- One row-independent distortion total after the same common shift. -/
structure Output (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cjet : ℝ) where
  N : ℕ
  half : ∀ n k, eps (shift D N) Cjet n k ≤ 1 / 2
  total : ℝ
  total_nonnegative : 0 ≤ total
  row_tsum_le : ∀ n, (∑' k, eps (shift D N) Cjet n k) ≤ total

theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ}
    (hCjet : 0 ≤ Cjet) : Nonempty (Output D Cjet) := by
  obtain ⟨N, hhalf⟩ := exists_shift_eps_le_half D Cjet
  let base : ℕ → ℝ := eps D Cjet 0
  let total := ShadowingTails.tail base 0
  have hbase0 : ∀ j, 0 ≤ base j := fun j => eps_nonnegative D hCjet 0 j
  have hbases : Summable base := summable_eps D 0
  refine ⟨{
    N := N
    half := hhalf
    total := total
    total_nonnegative := ShadowingTails.tail_nonneg hbase0 0
    row_tsum_le := ?_ }⟩
  intro n
  have heq : (∑' k, eps (shift D N) Cjet n k) =
      ShadowingTails.tail base (N + n) := by
    unfold ShadowingTails.tail
    apply tsum_congr
    intro k
    rw [eps_shift]
  rw [heq]
  exact ShadowingTails.tail_antitone hbases hbase0 (Nat.zero_le (N + n))

end ConfiguredGaugeJetUniformShift
