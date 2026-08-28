import UnitTangentIterates.ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly
import UnitTangentIterates.ConfiguredActualHalfScalarStart
import UnitTangentIterates.ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider

/-!
# Analytic-ceiling correlated direct assembly

This specializes the generic correlated capstone to the TeX-faithful
recursive constants `sourceKh = 5/6` and `analyticKhat`.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredMarkingAwareAnalyticKhatCombinedCorrelatedAssembly

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  VariableMarkedTube

/-- Final configured assembly once the exact correlated analytic recursion
and its selected endpoint caps have been constructed. -/
theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 Mend Cw : ℝ}
    (L : Output D
      (combinedConversionWithKhat D MA0 NA0 (analyticKhat D) sourceKh Mend)
      (physicalDefect D) Cw)
    {Qmodel : ℕ → Data} {C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel sourceKh C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {period : ℕ → ℕ → ℝ} {Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence (physicalDefect D) L.N))
      (rowP0 (shift D L.N))
      (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ analyticKhat D)
      (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
      (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence (physicalDefect D) L.N)
      (fun _ ↦ sourceKh) Qmax a MA NA K0 K1 K2)
    (R : CapFamily F
      (shiftSequence (endpointConversion D sourceKh Mend) L.N)
      (shiftSequence (physicalDefect D) L.N))
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics sourceKh
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
        (fun _ ↦ analyticKhat D)
        (shiftSequence (wideG1 D MA0 NA0) L.N)
        (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
        (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
          ((shift D L.N).Hs 0)) := by
  apply ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly.conclude L A hQ F R
  · intro n
    exact NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _
  · exact endpointConversion_nonneg D sourceKh_nonnegative sourceKh_lt_one
  · exact physicalDefect_nonneg D
  · intro n
    exact le_rfl
  · intro n
    rfl
  · exact hbasePhysical
  · exact hdirection L.N
  · simpa using hwidth L.N

end ConfiguredMarkingAwareAnalyticKhatCombinedCorrelatedAssembly

