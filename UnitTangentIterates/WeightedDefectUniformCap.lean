import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.WeightedRecursiveDefect

/-!
# A uniform strict cap for weighted recursive defects

A summable real sequence tends to zero and hence has bounded range.  Applied
to the nonnegative weighted defect, this supplies one positive constant which
strictly dominates every shifted pullback stage.
-/

noncomputable section

open Function Filter Topology

namespace PathMetric.WeightedRecursiveDefect

/-- Summability of the nonnegative weighted defect supplies a positive strict
uniform bound for all two-index pullback errors. -/
theorem exists_uniform_pullbackError_cap
    {K : ℝ} {d : ℕ → ℝ}
    (hK : 1 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable (weightedDefect K d)) :
    ∃ Mtotal : ℝ, 0 < Mtotal ∧
      ∀ n k, pullbackError K d n k < Mtotal := by
  have hbdd : BddAbove (Set.range (weightedDefect K d)) :=
    hsum.tendsto_atTop_zero.bddAbove_range
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨max 0 M + 1, by positivity, ?_⟩
  intro n k
  calc
    pullbackError K d n k ≤ weightedDefect K d (n + k) :=
      pullbackError_le_weightedDefect_shift hK hd n k
    _ ≤ M := hM ⟨n + k, rfl⟩
    _ ≤ max 0 M := le_max_right _ _
    _ < max 0 M + 1 := by linarith

/-- Unfolded form used directly by local approximate pullback capstones. -/
theorem exists_uniform_weighted_stage_cap
    {K : ℝ} {d : ℕ → ℝ}
    (hK : 1 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable (weightedDefect K d)) :
    ∃ Mtotal : ℝ, 0 < Mtotal ∧
      ∀ n k, K ^ k * d (n + k) < Mtotal := by
  simpa [pullbackError] using exists_uniform_pullbackError_cap hK hd hsum

end PathMetric.WeightedRecursiveDefect

namespace ConstructedConfiguredSequenceWeighted

open PathMetric.WeightedRecursiveDefect
open PathMetric.WeightedMarkedDefectThreshold

/-- The constructed configured sequence automatically has a positive strict
cap for every recursively weighted canonical marked defect. -/
theorem Data.exists_uniformCanonicalMarkedDefect_cap
    (D : Data) {K : ℝ} (hK : 1 ≤ K)
    (hthreshold : K * Real.exp (-(D.beta * D.deltaStep)) < 1) :
    ∃ Mtotal : ℝ, 0 < Mtotal ∧
      ∀ n k, K ^ k *
        canonicalMarkedDefect D.matchCoefficient 1 D.kstar D.kd
          D.beta D.Hs (n + k) < Mtotal := by
  let d : ℕ → ℝ := canonicalMarkedDefect
    D.matchCoefficient 1 D.kstar D.kd D.beta D.Hs
  have hd : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg
      (mul_nonneg (CurvatureStabilityL1.l1Modulus_nonneg _ _ _) (by norm_num))
      (by nlinarith [D.kstar_nonneg])
  have hsum : Summable (weightedDefect K d) :=
    D.summable_weightedCanonicalMarkedDefect (zero_le_one.trans hK) hthreshold
  simpa [d] using exists_uniform_weighted_stage_cap hK hd hsum

end ConstructedConfiguredSequenceWeighted
