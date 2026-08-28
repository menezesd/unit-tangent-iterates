import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.ConfiguredCanonicalPairSourceAutomatic
import UnitTangentIterates.ConfiguredActualSubunitCurvature

/-!
# Paper-facing scalar start with an actual subunit cap

This packages the same constructed model through width, diagonal separation,
finite-prefix shift, and the callback-free canonical pair source.  The coarse
configured `kstar` remains available for row estimates; the exact pair uses
the actual cap `1 / 2`.
-/

noncomputable section

open Set MarkedSpace

namespace ConfiguredActualHalfScalarStart

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
open ConfiguredPolynomialDiagonalStableRowDefectProvider
open ConstructedConfiguredInductiveTubeBudget.WeightedData

/-- Complete scalar/model input for the enriched recursive construction. -/
structure Output (MA NA : ℝ) where
  E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf
  direction : ℕ → ℂ
  Cw : ℝ
  Mend : ℝ
  Cw_nonnegative : 0 ≤ Cw
  Mend_positive : 0 < Mend
  direction_unit : ∀ n, ‖direction n‖ = 1
  model_width : ∀ n, Width.width
    (range (TwoCapPairsAssembly.front (E.data.kappas n)
      E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ Cw
  physicalDefect_lt : ∀ n, physicalDefect E.data n < Mend
  large : ExponentialDiagonalLargeSeparation.Output
    E.data (combinedConversionWithKhat E.data MA NA
      (analyticKhat E.data) sourceKh Mend)
      (physicalDefect E.data) Cw
  Q : ℕ → Data
  model_data : ∀ n,
    perim (Q n) = 2 * (shift E.data large.N).Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        ((shift E.data large.N).kappas n)
        (shift E.data large.N).model.thetaBase
        ((shift E.data large.N).Hs n)
  pair : ConfiguredCanonicalPairSource.Output
    (shift E.data large.N) Q sourceKh 0 0 (fun _ ↦ 0)

namespace Output

variable {MA NA : ℝ} (O : Output MA NA)

/-- The strengthened configured data after the diagonal prefix is removed. -/
def shiftedActual : ConstructedConfiguredSequenceWeighted.DataWithActualHalf :=
  shiftActualHalf O.E O.large.N

/-- The selected-inverse cap on the shifted construction is still exactly
`1 / 2`. -/
def actualCertificate :
    ConfiguredActualSubunitCurvature.Certificate
      (shift O.E.data O.large.N) :=
  ConfiguredActualSubunitCurvature.ofShiftedDataWithActualHalf O.E O.large.N

@[simp] theorem actualCertificate_k0 : O.actualCertificate.k0 = 1 / 2 := rfl

end Output

/-- Callback-free epsilon-level construction of the complete scalar start. -/
theorem exists_output_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) : Nonempty (Output MA NA) := by
  obtain ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, ⟨L⟩⟩ :=
    exists_actualHalf_widthData_and_combinedOutput_analytic_of_eps
      heps heps10 hMA hNA
  let Es := shiftActualHalf E L.N
  obtain ⟨Q, hQ, ⟨A⟩⟩ :=
    ConfiguredCanonicalPairSourceAutomatic.exists_output_of_cap Es.data
      sourceKh_nonnegative sourceKh_lt_one
      (Es.steering_le_half.trans half_le_sourceKh)
  refine ⟨⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM,
    L, Q, ?_, ?_⟩⟩
  · simpa [Es] using hQ
  · simpa [Es] using A

end ConfiguredActualHalfScalarStart
