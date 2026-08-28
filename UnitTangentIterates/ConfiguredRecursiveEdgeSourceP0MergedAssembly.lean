import UnitTangentIterates.ConfiguredRecursiveSourceP0MergedAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth

/-! # Merged sliced assembly at the genuine successor-edge floor -/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeSourceP0MergedAssembly

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore

theorem sliced_conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 Mend Cw : ℝ}
    (L : ExponentialDiagonalLargeSeparation.Output D
      (edgeCombinedConversion D MA0 NA0 (analyticKhat D) sourceKh Mend)
      (edgePhysicalDefect D) Cw)
    {Qmodel : ℕ → Data} {C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel sourceKh C0 K d)
    (hQ : ∀ n, perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {period : ℕ → ℕ → ℝ} {Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : SlicedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence (edgePhysicalDefect D) L.N))
      (edgeSourceP0 (shift D L.N))
      (edgeP1 (shift D L.N) MA0)
      (fun _ ↦ analyticKhat D)
      (edgeG1 (shift D L.N) MA0 NA0)
      (edgeCgWithKhat (shift D L.N) (analyticKhat D) MA0 NA0)
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence (edgePhysicalDefect D) L.N)
      (fun _ ↦ sourceKh) Qmax a MA NA K0 K1 K2)
    (R : SlicedCapFamily F
      (shiftSequence (edgeEndpointConversion D sourceKh Mend) L.N)
      (shiftSequence (edgePhysicalDefect D) L.N))
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics sourceKh
      (F.base.column.step.richStage n).terminalBase
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ (n + 1))))
    {direction : ℕ → ℂ} (hdirection : ∀ n, ‖direction n‖ = 1)
    (hwidth : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) :
    Nonempty (Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (fun n k ↦ F.columns k n)
      (rowError (shiftSequence (edgePhysicalDefect D) L.N))
      (edgeSourceP0 (shift D L.N))
      (edgeP1 (shift D L.N) MA0)
      (fun _ ↦ analyticKhat D)
      (edgeG1 (shift D L.N) MA0 NA0)
      (edgeCgWithKhat (shift D L.N) (analyticKhat D) MA0 NA0)
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2),
      PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
        ((shift D L.N).Hs 0)) := by
  apply ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly.sliced_conclude
    (pathConversion := edgeConversion D (analyticKhat D) MA0 NA0)
    (endpointConversion := edgeEndpointConversion D sourceKh Mend)
    L A hQ F R
  · exact edgeConversion_nonnegative D (analyticKhat D) MA0 NA0
  · exact edgeEndpointConversion_nonnegative D
      sourceKh_nonnegative sourceKh_lt_one
  · exact edgePhysicalDefect_nonnegative D
  · intro n
    change NormalPathC2IncrementVariableSpeed.c2ConstVar
      (edgeSourceP0 (shift D L.N) n)
      (edgeP1 (shift D L.N) MA0 n) (analyticKhat D)
      (edgeG1 (shift D L.N) MA0 NA0 n)
      (edgeCgWithKhat (shift D L.N) (analyticKhat D) MA0 NA0 n) ≤
        edgeConversion D (analyticKhat D) MA0 NA0 (L.N + n)
    rfl
  · intro n
    rfl
  · exact hbasePhysical
  · exact hdirection L.N
  · simpa using hwidth L.N

end ConfiguredRecursiveEdgeSourceP0MergedAssembly
