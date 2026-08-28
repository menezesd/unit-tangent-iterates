import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0

/-!
# Numerical reserve for a directly recosted recursive source

The direct recost construction enlarges the Jacobi-source coefficient from
`d` to `2*d`.  No new scalar threshold is needed: the configured source
denominator already contains the square of the original numerical ceiling,
and that ceiling is at least two.
-/

noncomputable section

namespace ConfiguredRecursiveSourceP0

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  GaugeRearFamilyFromFront
  InterpolationVariableSpeedConstants

/-- The configured row floor absorbs the doubled direct-recost source
constant using its existing squared numerical reserve. -/
theorem numerical_K_recost
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {Qmax : ℝ} (hQmax : 0 ≤ Qmax) (hQ : Qmax ≤ speedCap D n) :
    (2 * intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2) +
        analyticKhat D ^ 2 +
        2 * rearDriftConst Qmax sourceKh * successorKx sourceKh ≤
      1 / sourceP0 D n ^ 2 + analyticKhat D ^ 2 := by
  let d := intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh)
  let K := numericalKUpper D n
  let den := sourceDenom D n
  have hd0 : 0 ≤ d := by
    dsimp [d]
    unfold intrinsicSourceConst
    apply RearJacobiSourceCost.jacobiSourceConst_nonneg
    apply one_div_pos.mpr
    unfold intrinsicDerivativeConst
    rw [sourceKh_eq]
    positivity
  have hdrift := drift_le_upper D n hQmax hQ
  have hkx : 0 ≤ successorKx sourceKh := by
    unfold successorKx
    exact div_nonneg (mul_nonneg (by norm_num) sourceKh_nonnegative)
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hdu : 0 ≤ driftUpper D n := by
    unfold driftUpper rearDriftConst
    exact mul_nonneg (by
      unfold speedCap
      exact mul_nonneg (by norm_num)
        (add_nonneg zero_le_one (D.model.separation_pos n).le))
      (div_nonneg sourceKh_nonnegative (by
        rw [sourceKh_eq]
        norm_num))
  have hK0 : 2 ≤ K := by
    dsimp [K, numericalKUpper, d] at ⊢
    nlinarith [mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdu) hkx]
  have hleft :
      2 * d + 2 + 2 * rearDriftConst Qmax sourceKh * successorKx sourceKh ≤
        2 * K := by
    dsimp [K, numericalKUpper, d] at ⊢
    nlinarith
  have hKsq : 2 * K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hKden : K ^ 2 ≤ den := by
    dsimp [den, sourceDenom, K]
    have hf := (frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
      (D.model.separation_pos n)).le
    nlinarith [sq_nonneg (numericalAUpper D n)]
  have hden1 : 1 ≤ den := by
    dsimp [den, sourceDenom]
    have hf := (frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
      (D.model.separation_pos n)).le
    nlinarith [sq_nonneg (numericalAUpper D n),
      sq_nonneg (numericalKUpper D n)]
  have hdensq : den ≤ den ^ 2 := by nlinarith [sq_nonneg (den - 1)]
  rw [show 1 / sourceP0 D n ^ 2 = den ^ 2 by
    calc
      1 / sourceP0 D n ^ 2 = (1 / sourceP0 D n) ^ 2 := by ring
      _ = den ^ 2 := by rw [one_div_sourceP0]]
  dsimp [d] at hleft ⊢
  nlinarith

end ConfiguredRecursiveSourceP0

namespace ConfiguredRecursiveEdgeSourceP0

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareSmoothSource

/-- Successor-edge form consumed by the configured direct recost tower. -/
theorem numerical_K_recost
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    (2 * intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2) +
        analyticKhat D ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst
          (edgeSpeedCap D n) sourceKh * successorKx sourceKh ≤
      1 / edgeSourceP0 D n ^ 2 + analyticKhat D ^ 2 := by
  apply (ConfiguredRecursiveSourceP0.numerical_K_recost D (n + 1)
    (edgeSpeedCap_nonnegative D n) le_rfl).trans
  simpa [add_comm] using
    (add_le_add_right (one_div_sq_next_le_edge D n) (analyticKhat D ^ 2))

end ConfiguredRecursiveEdgeSourceP0
