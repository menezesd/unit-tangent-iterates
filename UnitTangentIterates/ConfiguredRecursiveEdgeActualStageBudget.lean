import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnScalarClosing

/-!
# Scalar budget for direct actual pullback stages

The direct path estimate and the nonaffine endpoint cap are charged
separately.  This is the arithmetic reason for the scalar factor
`4 * configuredTarget + 1`: the first summand pays for the canonically
recosted physical path and the final `1` pays for the endpoint cap.
-/

noncomputable section

open ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConstructedConfiguredInductiveTubeBudget.WeightedData

namespace ConfiguredRecursiveEdgeFiniteColumnScalarClosing

/-- A cap-aware actual-stage budget is bounded by the configured direct
diagonal.  Crucially, the endpoint cap is not multiplied by the path-metric
coefficient. -/
theorem capAwareBudget_le_directDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M K cap : ℝ} {j : ℕ}
    (hK0 : 0 ≤ K)
    (hK : K ≤ edgeConversion D (analyticKhat D) MA NA j)
    (hcap : cap ≤ edgeEndpointConversion D sourceKh M j *
      edgePhysicalDefect D (j + 1)) :
    K * (4 * configuredTarget E0 C0 C1 C2 *
        edgePhysicalDefect D (j + 1)) + cap ≤
      directDiagonal D MA NA E0 C0 C1 C2 M j := by
  let T : ℝ := 4 * configuredTarget E0 C0 C1 C2
  let A : ℝ := edgeConversion D (analyticKhat D) MA NA j
  let B : ℝ := edgeEndpointConversion D sourceKh M j
  let q : ℝ := edgePhysicalDefect D (j + 1)
  have hT0 : 0 ≤ T := mul_nonneg (by norm_num)
    (configuredTarget_nonnegative E0 C0 C1 C2)
  have hA0 : 0 ≤ A := edgeConversion_nonnegative D _ _ _ _
  have hB0 : 0 ≤ B := edgeEndpointConversion_nonnegative D
    sourceKh_nonnegative sourceKh_lt_one j
  have hq0 : 0 ≤ q := edgePhysicalDefect_nonnegative D (j + 1)
  have hfirst : K * (T * q) + cap ≤ A * (T * q) + B * q :=
    add_le_add
      (mul_le_mul_of_nonneg_right hK (mul_nonneg hT0 hq0)) hcap
  have hcoeff : T * A + B ≤ (T + 1) * (A + B) := by
    nlinarith [mul_nonneg hT0 hB0, hA0]
  calc
    K * (4 * configuredTarget E0 C0 C1 C2 *
          edgePhysicalDefect D (j + 1)) + cap =
        K * (T * q) + cap := rfl
    _ ≤ A * (T * q) + B * q := hfirst
    _ = (T * A + B) * q := by ring
    _ ≤ ((T + 1) * (A + B)) * q :=
      mul_le_mul_of_nonneg_right hcoeff hq0
    _ = directDiagonal D MA NA E0 C0 C1 C2 M j := by
      simp [directDiagonal, directConversion, directScale, weightedSequence,
        edgeCombinedConversion, T, A, B, q]

end ConfiguredRecursiveEdgeFiniteColumnScalarClosing
