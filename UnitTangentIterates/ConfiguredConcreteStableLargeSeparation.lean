import UnitTangentIterates.ConfiguredStableVariableTerminalCapstone
import UnitTangentIterates.ConfiguredRowCeilingPolynomialEnvelopes

/-!
# Concrete stable large separation for the configured ceilings

This specializes the stable scalar capstone to the actual interpolation
ceilings, widened once by fixed marking-jet bounds.  No abstract polynomial
envelope remains in the statement.
-/

noncomputable section

open Function Set

namespace ConfiguredConcreteStableLargeSeparation

open ConfiguredStableVariableTerminalCapstone
  ConfiguredRowCeilingPolynomialEnvelopes

theorem exists_widthData_and_concreteStableLargeSeparationOutput_of_eps
    {eps MA NA Cstable : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hCstable : 0 ≤ Cstable) :
    ∃ (D : ConstructedConfiguredSequenceWeighted.Data)
      (direction : ℕ → ℂ) (Cw : ℝ),
      0 ≤ Cw ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (D.kappas n)
          D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) ∧
      Nonempty (ConstructedStableRowDefectLargeSeparation.Output
        D
        (rowConversion D (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA))
        Cstable Cw) := by
  obtain ⟨D, direction, Cw, hCw, hdir, hwidth, hall⟩ :=
    exists_widthData_and_stable_largeSeparationOutput_of_eps heps heps10
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 8
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have hgamma4 : gamma < D.model.beta / 4 := by
    dsimp [gamma]
    nlinarith
  obtain ⟨A0, hA0, hgrowth⟩ :=
    exists_wide_c2ConstVar_growth_majorant D hMA hNA hgamma
  refine ⟨D, direction, Cw, hCw, hdir, hwidth, ?_⟩
  exact hall (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA)
    Cstable hCstable hA0 hgamma4 hgrowth

end ConfiguredConcreteStableLargeSeparation
