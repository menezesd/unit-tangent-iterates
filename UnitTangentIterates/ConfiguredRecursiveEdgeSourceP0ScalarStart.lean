import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0LargeSeparation
import UnitTangentIterates.ConfiguredCanonicalPairSourceAutomatic
import UnitTangentIterates.ConfiguredActualSubunitCurvature
import UnitTangentIterates.ConstructedPulseWidthC3Shift

/-! # Scalar start for the coherently edge-indexed recursive floor -/

noncomputable section

open Set MarkedSpace

namespace ConfiguredRecursiveEdgeSourceP0ScalarStart

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth
  ConstructedConfiguredInductiveTubeBudget.WeightedData

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
  model_width_add_two : ∀ n, Width.width
    (range (TwoCapPairsAssembly.front (E.data.kappas n)
      E.data.model.thetaBase (E.data.Hs n))) (direction n) + 2 ≤ Cw
  physicalDefect_lt : ∀ n, edgePhysicalDefect E.data n < Mend
  smooth : ConstructedPulseWidth.C3Certificate E.data
  large : ExponentialDiagonalLargeSeparation.Output E.data
    (edgeCombinedConversion E.data MA NA (analyticKhat E.data)
      sourceKh Mend)
    (edgePhysicalDefect E.data) Cw
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

def shiftedActual : ConstructedConfiguredSequenceWeighted.DataWithActualHalf :=
  shiftActualHalf O.E O.large.N

def actualCertificate :
    ConfiguredActualSubunitCurvature.Certificate
      (shift O.E.data O.large.N) :=
  ConfiguredActualSubunitCurvature.ofShiftedDataWithActualHalf O.E O.large.N

def shiftedC3 : ConstructedPulseWidth.C3Certificate
    (shift O.E.data O.large.N) :=
  O.smooth.shift O.large.N

@[simp] theorem actualCertificate_k0 : O.actualCertificate.k0 = 1 / 2 := rfl

end Output

theorem exists_output_of_eps
    {eps MA NA : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) : Nonempty (Output MA NA) := by
  obtain ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth,
      hwidth2, hdM, hC3, ⟨L⟩⟩ :=
    ConfiguredRecursiveEdgeSourceP0LargeSeparation.exists_actualHalf_widthDataC3_and_output_of_eps
      heps heps10 hMA hNA
  let Es := shiftActualHalf E L.N
  obtain ⟨Q, hQ, ⟨A⟩⟩ :=
    ConfiguredCanonicalPairSourceAutomatic.exists_output_of_cap Es.data
      sourceKh_nonnegative sourceKh_lt_one
      (Es.steering_le_half.trans half_le_sourceKh)
  refine ⟨⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hwidth2, hdM, hC3,
    L, Q, ?_, ?_⟩⟩
  · simpa [Es] using hQ
  · simpa [Es] using A

end ConfiguredRecursiveEdgeSourceP0ScalarStart
