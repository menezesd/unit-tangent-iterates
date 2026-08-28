import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth
import UnitTangentIterates.ConstructedPulseWidth

/-! # Large separation for the coherently edge-indexed recursive source -/

noncomputable section

open Function Set

namespace ConfiguredRecursiveEdgeSourceP0LargeSeparation

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth

set_option maxHeartbeats 2000000

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
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (E.data.kappas n)
          E.data.model.thetaBase (E.data.Hs n))) (direction n) + 2 ≤ Cw) ∧
      (∀ n, edgePhysicalDefect E.data n < Mend) ∧
      ConstructedPulseWidth.C3Certificate E.data ∧
      Nonempty (ExponentialDiagonalLargeSeparation.Output E.data
        (edgeCombinedConversion E.data MA NA (analyticKhat E.data)
          sourceKh Mend)
        (edgePhysicalDefect E.data) Cw) := by
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
  obtain ⟨A, hA, hedgeExp⟩ := exists_edgePhysicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, edgePhysicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    have he := Real.exp_le_exp.mpr harg
    calc
      edgePhysicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := hedgeExp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left he hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hMend.le hgamma
  let CwRear := Cw + 2
  have hCwRear : 0 ≤ CwRear := by dsimp [CwRear]; linarith
  have hwidthRear : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front (E.data.kappas n)
        E.data.model.thetaBase (E.data.Hs n))) (direction n) + 2 ≤ CwRear :=
    fun n => by dsimp [CwRear]; linarith [hwidth n]
  have hwidth' : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front (E.data.kappas n)
        E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ CwRear :=
    fun n => (hwidth n).trans (by dsimp [CwRear]; linarith)
  refine ⟨E, direction, CwRear, Mend, hCwRear, hMend, hdir,
    hwidth', hwidthRear, hdM, hC3, ?_⟩
  exact ExponentialDiagonalLargeSeparation.exists_output D
    (edgeCombinedConversion D MA NA (analyticKhat D) sourceKh Mend)
    (edgePhysicalDefect D)
    (edgeCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one)
    hC0 hA hb hgamma_b hCgrowth (edgePhysicalDefect_nonnegative D)
    (by intro n; simpa [b] using hedgeExp n) hCwRear

end ConfiguredRecursiveEdgeSourceP0LargeSeparation
