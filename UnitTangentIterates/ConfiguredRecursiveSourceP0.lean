import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteSource

/-!
# A polynomially weakened speed floor for recursive selected-rear sources

The configured interpolation has a uniform speed floor, but the selected-rear
drift constant grows with the row period cap.  The recursive source therefore
uses a smaller, row-dependent floor.  It is defined from the a priori cap
`3 * (1 + H_n)`, rather than from a subsequently selected diagonal radius, so
there is no circular dependence on large separation.
-/

noncomputable section

namespace ConfiguredRecursiveSourceP0

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRowCeilingPolynomialEnvelopes
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  GaugeRearFamilyFromFront
  InterpolationVariableSpeedConstants

def driftUpper (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  rearDriftConst (speedCap D n) sourceKh

def numericalAUpper
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  2 + 2 * analyticKhat D * driftUpper D n

def numericalKUpper
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2 +
    2 * driftUpper D n * successorKx sourceKh

/-- The local denominator contains the exact interpolation frame denominator
and a square reserve for each source numerical inequality. -/
def sourceDenom
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  frameD D.kstar D.kd (D.Hs n) (edgeEps D n) + 1 +
    numericalAUpper D n ^ 2 + numericalKUpper D n ^ 2

def sourceP0
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  1 / sourceDenom D n

theorem sourceDenom_pos
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 < sourceDenom D n := by
  unfold sourceDenom
  have hf := frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
    (D.model.separation_pos n)
  nlinarith [sq_nonneg (numericalAUpper D n),
    sq_nonneg (numericalKUpper D n)]

theorem sourceP0_pos
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 < sourceP0 D n :=
  one_div_pos.mpr (sourceDenom_pos D n)

theorem sourceP0_le_rowP0
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    sourceP0 D n ≤ rowP0 D n := by
  have hf := frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
    (D.model.separation_pos n)
  have hden : frameD D.kstar D.kd (D.Hs n) (edgeEps D n) ≤
      sourceDenom D n := by
    unfold sourceDenom
    nlinarith [sq_nonneg (numericalAUpper D n),
      sq_nonneg (numericalKUpper D n)]
  unfold sourceP0 rowP0 interpolationP0
  exact one_div_le_one_div_of_le hf hden

theorem one_div_sourceP0
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    1 / sourceP0 D n = sourceDenom D n := by
  unfold sourceP0
  field_simp [ne_of_gt (sourceDenom_pos D n)]

theorem sourceP0_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N n : ℕ) :
    sourceP0 (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) n =
      sourceP0 D (N + n) := by
  rfl

theorem drift_le_upper
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {Qmax : ℝ} (hQmax : 0 ≤ Qmax) (hQ : Qmax ≤ speedCap D n) :
    rearDriftConst Qmax sourceKh ≤ driftUpper D n := by
  unfold driftUpper rearDriftConst
  have hden : 0 ≤ 1 - sourceKh ^ 2 := by
    rw [sourceKh_eq]
    norm_num
  have hr : 0 ≤ sourceKh / (1 - sourceKh ^ 2) := by
    exact div_nonneg sourceKh_nonnegative hden
  exact mul_le_mul_of_nonneg_right hQ hr

theorem numerical_A
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {Qmax : ℝ} (hQmax : 0 ≤ Qmax) (hQ : Qmax ≤ speedCap D n) :
    2 + 2 * analyticKhat D * rearDriftConst Qmax sourceKh ≤
      1 / sourceP0 D n := by
  rw [one_div_sourceP0]
  have hdrift := drift_le_upper D n hQmax hQ
  have hkh := analyticKhat_nonnegative D
  have hleft : 2 + 2 * analyticKhat D * rearDriftConst Qmax sourceKh ≤
      numericalAUpper D n := by
    unfold numericalAUpper
    nlinarith
  have hsquare : numericalAUpper D n ≤ 1 + numericalAUpper D n ^ 2 := by
    nlinarith [sq_nonneg (numericalAUpper D n - 1 / 2)]
  unfold sourceDenom
  have hf := (frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
    (D.model.separation_pos n)).le
  exact hleft.trans (by
    nlinarith [hsquare, sq_nonneg (numericalKUpper D n)])

theorem numerical_K
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {Qmax : ℝ} (hQmax : 0 ≤ Qmax) (hQ : Qmax ≤ speedCap D n) :
    (intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2) +
        analyticKhat D ^ 2 +
        2 * rearDriftConst Qmax sourceKh * successorKx sourceKh ≤
      1 / sourceP0 D n ^ 2 + analyticKhat D ^ 2 := by
  have hdrift := drift_le_upper D n hQmax hQ
  have hkx : 0 ≤ successorKx sourceKh := by
    unfold successorKx
    exact div_nonneg (mul_nonneg (by norm_num) sourceKh_nonnegative)
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hK : intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2 +
        2 * rearDriftConst Qmax sourceKh * successorKx sourceKh ≤
      numericalKUpper D n := by
    unfold numericalKUpper
    nlinarith
  have hKden : numericalKUpper D n ≤ sourceDenom D n := by
    unfold sourceDenom
    have hf := (frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
      (D.model.separation_pos n)).le
    nlinarith [sq_nonneg (numericalAUpper D n),
      sq_nonneg (numericalKUpper D n - 1 / 2)]
  have hden1 : 1 ≤ sourceDenom D n := by
    unfold sourceDenom
    have hf := (frameD_pos (eps := edgeEps D n) D.kstar_nonneg D.kd_nonneg
      (D.model.separation_pos n)).le
    nlinarith [sq_nonneg (numericalAUpper D n),
      sq_nonneg (numericalKUpper D n)]
  have hdenSq : sourceDenom D n ≤ sourceDenom D n ^ 2 := by
    nlinarith [sq_nonneg (sourceDenom D n - 1)]
  rw [show 1 / sourceP0 D n ^ 2 = sourceDenom D n ^ 2 by
    calc
      1 / sourceP0 D n ^ 2 = (1 / sourceP0 D n) ^ 2 := by ring
      _ = sourceDenom D n ^ 2 := by rw [one_div_sourceP0]]
  nlinarith

end ConfiguredRecursiveSourceP0
