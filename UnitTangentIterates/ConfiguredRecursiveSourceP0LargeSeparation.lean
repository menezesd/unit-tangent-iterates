import UnitTangentIterates.ConfiguredRecursiveSourceP0Growth
import UnitTangentIterates.ConstructedPulseWidth

/-!
# Large separation for the recursive source speed floor

This is the scalar diagonal theorem with the row conversion evaluated at the
polynomially weakened recursive speed floor.
-/

noncomputable section

open Function Set

namespace ConfiguredRecursiveSourceP0LargeSeparation

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0Growth
  ConfiguredPolynomialDiagonalStableRowDefectProvider

set_option maxHeartbeats 2000000

theorem exists_actualHalf_widthData_and_output_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw Mend : ℝ),
      0 ≤ Cw ∧ 0 < Mend ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (E.data.kappas n)
          E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ Cw) ∧
      (∀ n, physicalDefect E.data n < Mend) ∧
      Nonempty (ExponentialDiagonalLargeSeparation.Output E.data
        (mergedCombinedConversion E.data MA NA (analyticKhat E.data)
          sourceKh Mend)
        (physicalDefect E.data) Cw) := by
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
  obtain ⟨A, hA, hdexp⟩ := exists_physicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, physicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    have he := Real.exp_le_exp.mpr harg
    calc
      physicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := by
        simpa [b] using hdexp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left he hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_mergedCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hMend.le hgamma
  refine ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, ?_⟩
  exact ExponentialDiagonalLargeSeparation.exists_output D
    (mergedCombinedConversion D MA NA (analyticKhat D) sourceKh Mend)
    (physicalDefect D)
    (mergedCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one)
    hC0 hA hb hgamma_b hCgrowth (physicalDefect_nonneg D)
    (by intro n; simpa [b] using hdexp n) hCw

/-- The same large-separation choice while retaining the canonical `C³`
endpoint certificate for the selected-rear source construction. -/
theorem exists_actualHalf_widthDataC3_and_output_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw Mend : ℝ),
      0 ≤ Cw ∧ 0 < Mend ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (E.data.kappas n)
          E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ Cw) ∧
      (∀ n, physicalDefect E.data n < Mend) ∧
      ConstructedPulseWidth.C3Certificate E.data ∧
      Nonempty (ExponentialDiagonalLargeSeparation.Output E.data
        (mergedCombinedConversion E.data MA NA (analyticKhat E.data)
          sourceKh Mend)
        (physicalDefect E.data) Cw) := by
  obtain ⟨E, direction, Cw, hCw, hdir, hwidth, hC3⟩ :=
    ConstructedPulseWidth.exists_actualHalf_widthDataC3_of_eps heps heps10
  let D := E.data
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by
    dsimp [gamma, b]
    nlinarith
  obtain ⟨A, hA, hdexp⟩ := exists_physicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, physicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    have he := Real.exp_le_exp.mpr harg
    calc
      physicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := by
        simpa [b] using hdexp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left he hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_mergedCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hMend.le hgamma
  refine ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, hC3, ?_⟩
  exact ExponentialDiagonalLargeSeparation.exists_output D
    (mergedCombinedConversion D MA NA (analyticKhat D) sourceKh Mend)
    (physicalDefect D)
    (mergedCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one)
    hC0 hA hb hgamma_b hCgrowth (physicalDefect_nonneg D)
    (by intro n; simpa [b] using hdexp n) hCw

end ConfiguredRecursiveSourceP0LargeSeparation
