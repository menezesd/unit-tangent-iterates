import UnitTangentIterates.ConfiguredDiagonalDirectAssembly
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-!
# Direct assembly specialized to the endpoint-corrected conversion
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredCombinedDiagonalDirectAssembly

open ConfiguredApproximateDefectPathRowwise
open ConfiguredCanonicalPairSource
open ConfiguredCombinedPhysicalDiagonalLargeSeparation
open ConfiguredInductiveTubeBudget
open ConfiguredPhysicalDiagonalRowBudget
open ConfiguredPolynomialDiagonalStableRowDefectProvider
open ConfiguredRowCeilingPolynomialEnvelopes
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open DiagonalEnrichedConstructionCoreDirectCapstone
open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalStageProducerFromRowBudget
open ExponentialDiagonalLargeSeparation

theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 kh Mend Cw : ℝ}
    (L : Output D (combinedConversion D MA0 NA0 kh Mend)
      (physicalDefect D) Cw)
    {Qmodel : ℕ → Data} {C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {period : ℕ → ℕ → ℝ}
    {GaugeCertificate : GaugeFamily
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence (physicalDefect D) L.N))
      (rowP0 (shift D L.N))
      (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ (shift D L.N).kstar)
      (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCg D MA0 NA0) L.N)
      (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence (physicalDefect D) L.N))
      (rowP0 (shift D L.N))
      (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ (shift D L.N).kstar)
      (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCg D MA0 NA0) L.N)
      (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence (physicalDefect D) L.N) GaugeCertificate
      a MA NA K0 K1 K2)
    (G : PhysicalProducer F kh ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2))
    {direction : ℕ → ℂ}
    (hdirection : ∀ n, ‖direction n‖ = 1)
    (hwidth : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (fun n k ↦ columns F.baseProvider F.mapProvider k n)
        (rowError (shiftSequence (physicalDefect D) L.N))
        (rowP0 (shift D L.N))
        (shiftSequence (wideP1 D MA0) L.N)
        (fun _ ↦ (shift D L.N).kstar)
        (shiftSequence (wideG1 D MA0 NA0) L.N)
        (shiftSequence (wideCg D MA0 NA0) L.N)
        (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
          ((shift D L.N).Hs 0)) := by
  apply ConfiguredDiagonalDirectAssembly.conclude L A hQ F G
  · exact combinedConversion_nonneg D A.input.kh_nonneg A.input.kh_lt_one
  · exact physicalDefect_nonneg D
  · intro n
    change ConfiguredPhysicalDiagonalRowBudget.conversion D MA0 NA0 (L.N + n) ≤
      ConfiguredPhysicalDiagonalRowBudget.conversion D MA0 NA0 (L.N + n) +
        endpointConversion D kh Mend (L.N + n)
    exact le_add_of_nonneg_right
      (endpointConversion_nonneg D A.input.kh_nonneg A.input.kh_lt_one (L.N + n))
  · exact hdirection L.N
  · simpa using hwidth L.N

end ConfiguredCombinedDiagonalDirectAssembly
