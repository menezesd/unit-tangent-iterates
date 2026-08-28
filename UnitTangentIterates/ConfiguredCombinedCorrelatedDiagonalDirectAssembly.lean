import UnitTangentIterates.ConfiguredCorrelatedDiagonalDirectAssembly
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-!
# Correlated direct assembly with the endpoint-corrected conversion
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredCombinedCorrelatedDiagonalDirectAssembly

open ConfiguredApproximateDefectPathRowwise
open ConfiguredCanonicalPairSource
open ConfiguredCombinedPhysicalDiagonalLargeSeparation
open ConfiguredInductiveTubeBudget
open ConfiguredPhysicalDiagonalRowBudget
open ConfiguredPolynomialDiagonalStableRowDefectProvider
open ConfiguredRowCeilingPolynomialEnvelopes
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ExponentialDiagonalLargeSeparation
open FiniteSmoothRearFamilyCorrelatedPhysicalCore
open VariableMarkedTube

theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 kh0 Mend Cw : ℝ}
    (L : Output D (combinedConversion D MA0 NA0 kh0 Mend)
      (physicalDefect D) Cw)
    {Qmodel : ℕ → Data} {C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {period : ℕ → ℕ → ℝ} {sourceKh Qmax Mtotal : ℕ → ℝ}
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
      period (shiftSequence (physicalDefect D) L.N)
      sourceKh Qmax Mtotal a MA NA K0 K1 K2)
    (R : CapFamily F
      (shiftSequence (endpointConversion D kh0 Mend) L.N)
      (shiftSequence (physicalDefect D) L.N))
    (hkh : ∀ n, sourceKh n = kh0)
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ (n + 1))))
    {direction : ℕ → ℂ}
    (hdirection : ∀ n, ‖direction n‖ = 1)
    (hwidth : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (fun n k ↦ F.columns k n)
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
  apply ConfiguredCorrelatedDiagonalDirectAssembly.conclude L A hQ F R
  · intro n
    exact NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _
  · exact endpointConversion_nonneg D A.input.kh_nonneg A.input.kh_lt_one
  · exact physicalDefect_nonneg D
  · intro n
    exact le_rfl
  · exact hkh
  · exact hbasePhysical
  · exact hdirection L.N
  · simpa using hwidth L.N

end ConfiguredCombinedCorrelatedDiagonalDirectAssembly
