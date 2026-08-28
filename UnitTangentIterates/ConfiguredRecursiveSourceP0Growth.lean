import UnitTangentIterates.ConfiguredRecursiveSourceP0
import UnitTangentIterates.ConstructedRowCPolynomialGrowthVariableP0
import UnitTangentIterates.ConfiguredMarkingAwareMergedEndpointGrowth

/-!
# Polynomial growth for the recursive source speed floor

The selected-rear drift grows linearly with the row perimeter.  The recursive
source floor is therefore weakened polynomially.  This file proves that its
inverse has polynomial growth and incorporates it into the configured row
conversion and the merged endpoint correction.
-/

noncomputable section

namespace ConfiguredRecursiveSourceP0Growth

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedRowCPolynomialGrowth
  ConstructedRowCPolynomialGrowthVariableP0
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  GaugeMarkedDataOfRearFamily
  GaugeRearFamilyFromFront
  InterpolationFrame
  InterpolationPathDist
  InterpolationVariableSpeedConstants
  NormalPathC2IncrementVariableSpeed

def driftCoeff : ℝ := 3 * rearKappa1 sourceKh

def numericalACoeff (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  2 + 2 * analyticKhat D * driftCoeff

def numericalKCoeff : ℝ :=
  intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2 +
    2 * driftCoeff * successorKx sourceKh

def sourceDenomCoeff (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  frameCap D + 1 + numericalACoeff D ^ 2 + numericalKCoeff ^ 2

theorem driftCoeff_nonnegative : 0 ≤ driftCoeff := by
  unfold driftCoeff
  exact mul_nonneg (by norm_num)
    (rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one)

theorem numericalACoeff_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ numericalACoeff D := by
  unfold numericalACoeff
  exact add_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) (analyticKhat_nonnegative D))
      driftCoeff_nonnegative)

theorem intrinsicDerivativeConst_positive :
    0 < intrinsicDerivativeConst sourceKh := by
  unfold intrinsicDerivativeConst
  rw [sourceKh_eq]
  positivity

theorem intrinsicSourceConst_nonnegative :
    0 ≤ intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) := by
  unfold intrinsicSourceConst
  exact RearJacobiSourceCost.jacobiSourceConst_nonneg
    (one_div_pos.mpr intrinsicDerivativeConst_positive)

theorem successorKx_nonnegative : 0 ≤ successorKx sourceKh := by
  unfold successorKx
  rw [sourceKh_eq]
  positivity

theorem numericalKCoeff_nonnegative : 0 ≤ numericalKCoeff := by
  unfold numericalKCoeff
  exact add_nonneg
    (add_nonneg intrinsicSourceConst_nonnegative (by norm_num))
    (mul_nonneg
      (mul_nonneg (by norm_num) driftCoeff_nonnegative)
      successorKx_nonnegative)

theorem sourceDenomCoeff_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ sourceDenomCoeff D := by
  unfold sourceDenomCoeff
  nlinarith [frameCap_pos D, sq_nonneg (numericalACoeff D),
    sq_nonneg numericalKCoeff]

theorem driftUpper_eq
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    driftUpper D n = driftCoeff * (1 + D.Hs n) := by
  unfold driftUpper driftCoeff speedCap rearDriftConst rearKappa1
  ring

theorem numericalAUpper_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    numericalAUpper D n ≤ numericalACoeff D * (1 + D.Hs n) := by
  rw [show numericalAUpper D n =
      2 + 2 * analyticKhat D * driftUpper D n by rfl, driftUpper_eq]
  unfold numericalACoeff
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hk := analyticKhat_nonnegative D
  have hd := driftCoeff_nonnegative
  nlinarith

theorem numericalKUpper_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    numericalKUpper D n ≤ numericalKCoeff * (1 + D.Hs n) := by
  rw [show numericalKUpper D n =
      intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2 +
        2 * driftUpper D n * successorKx sourceKh by rfl,
    driftUpper_eq]
  unfold numericalKCoeff
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hs := intrinsicSourceConst_nonnegative
  have hk := successorKx_nonnegative
  have hd := driftCoeff_nonnegative
  nlinarith

theorem frameD_le_frameCap
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    InterpolationVariableSpeedConstants.frameD D.kstar D.kd
        (D.Hs n) (ConfiguredApproximateDefectPathRowwise.edgeEps D n) ≤
      frameCap D := by
  have hi : 1 / (2 * D.Hs n) ≤ 1 / (2 * D.Hs 0) := by
    exact one_div_le_one_div_of_le
      (mul_pos (by norm_num) D.separation_zero_pos)
      (mul_le_mul_of_nonneg_left (D.separation_lower n) (by norm_num))
  have hi2 : 1 / (2 * D.Hs n) ^ 2 ≤ 1 / (2 * D.Hs 0) ^ 2 := by
    have hmul : 2 * D.Hs 0 ≤ 2 * D.Hs n :=
      mul_le_mul_of_nonneg_left (D.separation_lower n) (by norm_num)
    have hsq : (2 * D.Hs 0) ^ 2 ≤ (2 * D.Hs n) ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg (by norm_num) D.separation_zero_pos.le)
        (mul_nonneg (by norm_num) (D.model.separation_pos n).le)).2 hmul
    exact one_div_le_one_div_of_le
      (sq_pos_of_pos (mul_pos (by norm_num) D.separation_zero_pos))
      hsq
  have hfacLower : 2 * D.Hs n ≤
      costFac D.kstar (D.Hs n)
        (ConfiguredApproximateDefectPathRowwise.edgeEps D n) := by
    unfold costFac
    have hr := rate1Bound_nonneg D.kstar_nonneg
      (D.model.separation_pos n).le
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
    have he := Real.one_le_exp hr
    nlinarith [D.model.separation_pos n]
  have hfacPos := costFac_pos
    (kstar := D.kstar)
    (eps := ConfiguredApproximateDefectPathRowwise.edgeEps D n)
    (D.model.separation_pos n)
  have hInv : 1 / costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) ≤
      1 / (2 * D.Hs n) :=
    one_div_le_one_div_of_le
      (mul_pos (by norm_num) (D.model.separation_pos n)) hfacLower
  have hInv2 : 1 / costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) ^ 2 ≤
      1 / (2 * D.Hs n) ^ 2 := by
    exact one_div_le_one_div_of_le
      (sq_pos_of_pos (mul_pos (by norm_num) (D.model.separation_pos n)))
      ((sq_le_sq₀
        (mul_nonneg (by norm_num) (D.model.separation_pos n).le)
        hfacPos.le).2 hfacLower)
  unfold InterpolationVariableSpeedConstants.frameD frameCap
  linarith

def inverseSourceP0Envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun n ↦ 1 / sourceP0 D n) where
  coeff := sourceDenomCoeff D
  degree := 2
  coeff_nonneg := sourceDenomCoeff_nonnegative D
  value_nonneg n := (one_div_pos.mpr (sourceP0_pos D n)).le
  bound n := by
    rw [one_div_sourceP0]
    let z : ℝ := 1 + D.Hs n
    have hz1 : 1 ≤ z := by dsimp [z]; linarith [(D.model.separation_pos n).le]
    have hz0 : 0 ≤ z := zero_le_one.trans hz1
    have hA := numericalAUpper_le D n
    have hK := numericalKUpper_le D n
    have hA0 : 0 ≤ numericalAUpper D n := by
      unfold numericalAUpper
      exact add_nonneg (by norm_num)
        (mul_nonneg
          (mul_nonneg (by norm_num) (analyticKhat_nonnegative D))
          (by rw [driftUpper_eq]; exact mul_nonneg driftCoeff_nonnegative hz0))
    have hK0 : 0 ≤ numericalKUpper D n := by
      unfold numericalKUpper
      exact add_nonneg
        (add_nonneg intrinsicSourceConst_nonnegative (by norm_num))
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (by rw [driftUpper_eq]; exact mul_nonneg driftCoeff_nonnegative hz0))
          successorKx_nonnegative)
    have hA2 : numericalAUpper D n ^ 2 ≤
        numericalACoeff D ^ 2 * z ^ 2 := by
      calc
        _ ≤ (numericalACoeff D * z) ^ 2 :=
          (sq_le_sq₀ hA0 (mul_nonneg (numericalACoeff_nonnegative D) hz0)).2
            (by simpa [z] using hA)
        _ = _ := by ring
    have hK2 : numericalKUpper D n ^ 2 ≤
        numericalKCoeff ^ 2 * z ^ 2 := by
      calc
        _ ≤ (numericalKCoeff * z) ^ 2 :=
          (sq_le_sq₀ hK0 (mul_nonneg numericalKCoeff_nonnegative hz0)).2
            (by simpa [z] using hK)
        _ = _ := by ring
    have hf := frameD_le_frameCap D n
    have hf0 := frameCap_pos D |>.le
    unfold sourceDenom sourceDenomCoeff
    nlinarith [sq_nonneg z, sq_nonneg (z - 1)]

def conversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ c2ConstVar (sourceP0 D n) (wideP1 D MA n) khat
    (wideG1 D MA NA n) (wideCgWithKhat D khat MA NA n)

theorem conversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) (n : ℕ) : 0 ≤ conversion D khat MA NA n :=
  c2ConstVar_nonneg _ _ _ _ _

theorem exists_conversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat MA NA gamma : ℝ}
    (hkhat : 0 ≤ khat) (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      conversion D khat MA NA n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  exact exists_c2ConstVar_growth_majorant_of_inverseEnvelope
    (fun n ↦ (D.model.separation_pos n).le) (sourceP0_pos D)
    (inverseSourceP0Envelope D) (wideP1Envelope D hMA)
    (constantKhatEnvelope D hkhat) (wideG1Envelope D hMA hNA)
    (wideCgWithKhatEnvelope D hkhat hMA hNA) hgamma

def mergedCombinedConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ) : ℕ → ℝ :=
  fun n ↦ conversion D khat MA NA n +
    ConfiguredMarkingAwareMergedEndpointGrowth.mergedEndpointConversion D kh M n

theorem mergedCombinedConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ n, 0 ≤ mergedCombinedConversion D MA NA khat kh M n := by
  intro n
  exact add_nonneg (conversion_nonnegative D khat MA NA n)
    (ConfiguredMarkingAwareMergedEndpointGrowth.mergedEndpointConversion_nonnegative
      D hkh0 hkh1 n)

theorem exists_mergedCombinedConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M gamma : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      mergedCombinedConversion D MA NA khat kh M n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_conversion_growth_majorant D hkhat hMA hNA hgamma
  obtain ⟨B, hB0, hB⟩ :=
    ConfiguredMarkingAwareMergedEndpointGrowth.exists_mergedEndpointConversion_growth_majorant
      D hkh0 hkh1 hM hgamma
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro n
  unfold mergedCombinedConversion
  calc
    _ ≤ A * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) +
        B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) :=
      add_le_add (hA n) (hB n)
    _ = (A + B) * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by ring

end ConfiguredRecursiveSourceP0Growth
