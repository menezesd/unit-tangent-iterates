import UnitTangentIterates.ConfiguredMarkingAwareAnalyticKhatBaseColumnCap
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider

/-! # Growth of the merged base/successor endpoint coefficient -/

noncomputable section

open Function

namespace ConfiguredMarkingAwareMergedEndpointGrowth

open ConfiguredCorrelatedBaseColumnCap
  ConfiguredGaugeEndpointCoefficientGrowth
  ConfiguredGaugeEndpointLinearRadius
  FiniteSmoothRearFamilyMarkingAwareCappedProvider

def baseEll (D : ConstructedConfiguredSequenceWeighted.Data) : ℕ → ℝ :=
  fun n ↦ 2 * D.Hs n

def baseLmax (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    ℕ → ℝ :=
  fun n ↦ (2 * D.Hs n) * (Real.exp (baseKappa D * M) + 1)

def baseLength (D : ConstructedConfiguredSequenceWeighted.Data) : ℕ → ℝ :=
  fun n ↦ 2 * D.Hs n

def baseLinearInputBounds
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    LinearInputBounds D.Hs (baseEll D) (baseLmax D M) (baseLength D) where
  ellCoeff := 2
  maxCoeff := 2 * (Real.exp (baseKappa D * M) + 1)
  lengthCoeff := 2
  ellCoeff_nonneg := by norm_num
  maxCoeff_nonneg := mul_nonneg (by norm_num)
    (add_nonneg (Real.exp_pos _).le zero_le_one)
  lengthCoeff_nonneg := by norm_num
  H_nonneg n := (D.model.separation_pos n).le
  ell_nonneg n := mul_nonneg (by norm_num) (D.model.separation_pos n).le
  max_nonneg n := mul_nonneg
    (mul_nonneg (by norm_num) (D.model.separation_pos n).le)
    (add_nonneg (Real.exp_pos _).le zero_le_one)
  length_nonneg n := mul_nonneg (by norm_num) (D.model.separation_pos n).le
  ell_le n := by
    unfold baseEll
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left zero_le_one) (by norm_num)
  max_le n := by
    have he : 0 ≤ Real.exp (baseKappa D * M) + 1 :=
      add_nonneg (Real.exp_pos _).le zero_le_one
    calc
      baseLmax D M n ≤
          2 * (1 + D.Hs n) * (Real.exp (baseKappa D * M) + 1) := by
        unfold baseLmax
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left zero_le_one) (by norm_num)) he
      _ = 2 * (Real.exp (baseKappa D * M) + 1) * (1 + D.Hs n) := by ring
  length_le n := by
    unfold baseLength
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left zero_le_one) (by norm_num)

theorem baseKappa_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) : 0 ≤ baseKappa D :=
  mul_nonneg (by norm_num) D.kstar_nonneg

theorem baseKappa2_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) : 0 ≤ baseKappa2 D := by
  unfold baseKappa2
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) D.kd_nonneg)
      (mul_nonneg (by norm_num) D.kstar_nonneg))
    (mul_nonneg (by norm_num) (sq_nonneg D.kstar))

theorem baseEndpointConversion_eq
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    baseEndpointConversion D M =
      endpointLinearCoeff (baseEll D) (baseLmax D M)
        (fun _ ↦ baseKappa D) (fun _ ↦ baseKappa2 D)
        (baseLength D) (fun _ ↦ D.kstar) (fun _ ↦ D.kd) M := by
  funext n
  simp only [baseEndpointConversion, baseFirstCoeff, baseSecondCoeff,
    baseEll, baseLmax, baseLength, endpointLinearCoeff,
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst]
  ring_nf

theorem baseEndpointConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    ∀ n, 0 ≤ baseEndpointConversion D M n := by
  rw [baseEndpointConversion_eq]
  apply endpointLinearCoeff_nonneg
  · intro n
    unfold baseLmax
    exact mul_nonneg (mul_nonneg (by norm_num) (D.model.separation_pos n).le)
      (add_nonneg (Real.exp_pos _).le zero_le_one)
  · intro n
    exact baseKappa_nonnegative D

theorem exists_baseEndpointConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {M gamma : ℝ} (hM : 0 ≤ M) (hgamma : 0 < gamma) :
    ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ n,
      baseEndpointConversion D M n ≤
        E0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  rw [baseEndpointConversion_eq]
  exact exists_endpointLinearCoeff_growth_majorant
    (baseLinearInputBounds D M) (baseKappa_nonnegative D)
    (baseKappa2_nonnegative D) hM D.kstar_nonneg D.kd_nonneg hgamma

def mergedEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data) (kh M : ℝ) :
    ℕ → ℝ :=
  mergedConversion (baseEndpointConversion D M)
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion D kh M)

theorem mergedEndpointConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh M : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ n, 0 ≤ mergedEndpointConversion D kh M n := by
  intro n
  exact (baseEndpointConversion_nonnegative D M n).trans (le_max_left _ _)

theorem exists_mergedEndpointConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {kh M gamma : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hM : 0 ≤ M) (hgamma : 0 < gamma) :
    ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ n,
      mergedEndpointConversion D kh M n ≤
        E0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_baseEndpointConversion_growth_majorant D hM hgamma
  obtain ⟨B, hB0, hB⟩ :=
    ConfiguredGaugeEndpointCoefficientGrowth.exists_endpointLinearCoeff_growth_majorant
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.configuredLinearInputBounds D)
      (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkh0 hkh1)
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkh0 hkh1)
      hM D.kstar_nonneg D.kd_nonneg hgamma
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro n
  unfold mergedEndpointConversion mergedConversion
  have hz : 0 ≤ (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
    positivity
  apply max_le
  · apply (hA n).trans
    calc
      A * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) =
          A * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) := by ring
      _ ≤ (A + B) * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB0) hz
      _ = (A + B) * (1 + D.Hs n) ^ 2 *
          Real.exp (gamma * D.Hs n) := by ring
  · have hs := hB n
    change ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion
      D kh M n ≤ B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) at hs
    apply hs.trans
    calc
      B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) =
          B * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) := by ring
      _ ≤ (A + B) * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA0) hz
      _ = (A + B) * (1 + D.Hs n) ^ 2 *
          Real.exp (gamma * D.Hs n) := by ring

def mergedCombinedConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ) : ℕ → ℝ :=
  ConfiguredGaugeEndpointLinearRadius.combinedConversion
    (ConfiguredPhysicalDiagonalRowBudget.conversionWithKhat D khat MA NA)
    (mergedEndpointConversion D kh M)

theorem mergedCombinedConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ n, 0 ≤ mergedCombinedConversion D MA NA khat kh M n := by
  apply ConfiguredGaugeEndpointLinearRadius.combinedConversion_nonneg
  · intro n
    exact NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _
  · exact mergedEndpointConversion_nonnegative D hkh0 hkh1

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
    ConfiguredRowCeilingPolynomialEnvelopes.exists_wide_c2ConstVar_growth_majorant_withKhat
      D hkhat hMA hNA hgamma
  obtain ⟨B, hB0, hB⟩ :=
    exists_mergedEndpointConversion_growth_majorant D hkh0 hkh1 hM hgamma
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro n
  unfold mergedCombinedConversion ConfiguredGaugeEndpointLinearRadius.combinedConversion
  calc
    _ ≤ A * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) +
        B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) :=
      add_le_add (hA n) (hB n)
    _ = (A + B) * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by ring

/-- Epsilon-level actual-half scalar output reserving both the configured
base marking correction and every marking-aware successor correction. -/
theorem exists_actualHalf_widthData_and_mergedOutput_analytic_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw Mend : ℝ),
      0 ≤ Cw ∧ 0 < Mend ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (Set.range (TwoCapPairsAssembly.front (E.data.kappas n)
          E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ Cw) ∧
      (∀ n, ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
        E.data n < Mend) ∧
      Nonempty (ExponentialDiagonalLargeSeparation.Output E.data
        (mergedCombinedConversion E.data MA NA
          (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat E.data)
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh Mend)
        (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect E.data)
        Cw) := by
  obtain ⟨E, direction, Cw, hCw, hdir, hwidth⟩ :=
    ConstructedPulseWidth.exists_actualHalf_widthData_of_eps heps heps10
  let D := E.data
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by
    dsimp [gamma, b]
    nlinarith
  obtain ⟨A, hA, hdexp⟩ :=
    ConfiguredPolynomialDiagonalStableRowDefectProvider.exists_physicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n,
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    have he := Real.exp_le_exp.mpr harg
    calc
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D n ≤
          A * Real.exp (-(b * D.Hs n)) := by
        simpa [b] using hdexp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left he hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_mergedCombinedConversion_growth_majorant D hMA hNA
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat_nonnegative D)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
      hMend.le hgamma
  refine ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, ?_⟩
  exact ExponentialDiagonalLargeSeparation.exists_output D
    (mergedCombinedConversion D MA NA
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh Mend)
    (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D)
    (mergedCombinedConversion_nonnegative D
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat_nonnegative D)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one)
    hC0 hA hb hgamma_b hCgrowth
    (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect_nonneg D)
    (by intro n; simpa [b] using hdexp n) hCw

end ConfiguredMarkingAwareMergedEndpointGrowth
