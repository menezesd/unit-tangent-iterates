import UnitTangentIterates.ConfiguredConcreteStableLargeSeparation
import UnitTangentIterates.ConfiguredPolynomialDiagonalStableRowDefectProvider
import UnitTangentIterates.ExponentialDiagonalLargeSeparation

/-!
# Large separation for the physical perimeter-scaled diagonal error

The exact source coefficient is `2 H_j`.  This theorem combines its
degree-one exponential absorption with the explicit widened row ceilings and
produces all scalar tube and closing budgets.
-/

noncomputable section

open Function Set

namespace ConfiguredPhysicalDiagonalLargeSeparation

open ConfiguredStableVariableTerminalCapstone
open ConfiguredRowCeilingPolynomialEnvelopes
open ConfiguredPolynomialDiagonalStableRowDefectProvider

theorem exists_widthData_and_physicalDiagonalOutput_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    ∃ (D : ConstructedConfiguredSequenceWeighted.Data)
      (direction : ℕ → ℂ) (Cw : ℝ),
      0 ≤ Cw ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (D.kappas n)
          D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) ∧
      Nonempty (ExponentialDiagonalLargeSeparation.Output
        D
        (rowConversion D (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA))
        (physicalDefect D) Cw) := by
  obtain ⟨D, direction, Cw, hCw, hdir, hwidth, -⟩ :=
    exists_widthData_and_stable_largeSeparationOutput_of_eps heps heps10
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by
    dsimp [gamma, b]
    nlinarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_wide_c2ConstVar_growth_majorant D hMA hNA hgamma
  obtain ⟨A, hA, hdexp⟩ := exists_physicalDefect_exp_bound D
  refine ⟨D, direction, Cw, hCw, hdir, hwidth, ?_⟩
  exact ExponentialDiagonalLargeSeparation.exists_output D
    (rowConversion D (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA))
    (physicalDefect D)
    (fun n ↦ NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _)
    hC0 hA hb hgamma_b hCgrowth (physicalDefect_nonneg D) (by
      intro n
      simpa [b] using hdexp n) hCw

end ConfiguredPhysicalDiagonalLargeSeparation
