import UnitTangentIterates.ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly
import UnitTangentIterates.ConfiguredRecursiveSourceP0Growth

/-! # Final configured assembly at the polynomial recursive speed floor -/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0MergedAssembly

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredInductiveTubeBudget
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0
  ConfiguredRecursiveSourceP0Growth
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  VariableMarkedTube

/-- The generic marking-aware diagonal capstone specialized to `sourceP0`.
The large-separation conversion is definitionally the sum of the variable-P0
path conversion and the merged endpoint conversion. -/
theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 Mend Cw : ℝ}
    (L : ExponentialDiagonalLargeSeparation.Output D
      (ConfiguredRecursiveSourceP0Growth.mergedCombinedConversion
        D MA0 NA0 (analyticKhat D) sourceKh Mend)
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
      (sourceP0 (shift D L.N))
      (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ analyticKhat D)
      (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
      (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence (physicalDefect D) L.N)
      (fun _ ↦ sourceKh) Qmax a MA NA K0 K1 K2)
    (R : CapFamily F
      (shiftSequence (mergedEndpointConversion D sourceKh Mend) L.N)
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
        (sourceP0 (shift D L.N))
        (shiftSequence (wideP1 D MA0) L.N)
        (fun _ ↦ analyticKhat D)
        (shiftSequence (wideG1 D MA0 NA0) L.N)
        (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
        (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
          ((shift D L.N).Hs 0)) := by
  apply ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly.conclude
    (pathConversion := conversion D (analyticKhat D) MA0 NA0)
    (endpointConversion := mergedEndpointConversion D sourceKh Mend)
    L A hQ F R
  · exact conversion_nonnegative D (analyticKhat D) MA0 NA0
  · exact mergedEndpointConversion_nonnegative D
      sourceKh_nonnegative sourceKh_lt_one
  · exact physicalDefect_nonneg D
  · intro n
    simpa [ConfiguredRecursiveSourceP0Growth.conversion, sourceP0_shift,
      shiftSequence] using
      (le_refl (NormalPathC2IncrementVariableSpeed.c2ConstVar
        (sourceP0 D (L.N + n)) (wideP1 D MA0 (L.N + n))
        (analyticKhat D) (wideG1 D MA0 NA0 (L.N + n))
        (wideCgWithKhat D (analyticKhat D) MA0 NA0 (L.N + n))))
  · intro n
    rfl
  · exact hbasePhysical
  · exact hdirection L.N
  · simpa using hwidth L.N

/-- `sourceP0` specialization for the invariant-indexed reachable core. -/
theorem sliced_conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {MA0 NA0 Mend Cw : ℝ}
    (L : ExponentialDiagonalLargeSeparation.Output D
      (ConfiguredRecursiveSourceP0Growth.mergedCombinedConversion
        D MA0 NA0 (analyticKhat D) sourceKh Mend)
      (physicalDefect D) Cw)
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
      (rowError (shiftSequence (physicalDefect D) L.N))
      (sourceP0 (shift D L.N)) (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ analyticKhat D) (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence (physicalDefect D) L.N) (fun _ ↦ sourceKh) Qmax
      a MA NA K0 K1 K2)
    (R : SlicedCapFamily F
      (shiftSequence (mergedEndpointConversion D sourceKh Mend) L.N)
      (shiftSequence (physicalDefect D) L.N))
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
      (rowError (shiftSequence (physicalDefect D) L.N))
      (sourceP0 (shift D L.N)) (shiftSequence (wideP1 D MA0) L.N)
      (fun _ ↦ analyticKhat D) (shiftSequence (wideG1 D MA0 NA0) L.N)
      (shiftSequence (wideCgWithKhat D (analyticKhat D) MA0 NA0) L.N)
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2),
      PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
        ((shift D L.N).Hs 0)) := by
  apply ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly.sliced_conclude
    (pathConversion := conversion D (analyticKhat D) MA0 NA0)
    (endpointConversion := mergedEndpointConversion D sourceKh Mend)
    L A hQ F R
  · exact conversion_nonnegative D (analyticKhat D) MA0 NA0
  · exact mergedEndpointConversion_nonnegative D
      sourceKh_nonnegative sourceKh_lt_one
  · exact physicalDefect_nonneg D
  · intro n
    simpa [ConfiguredRecursiveSourceP0Growth.conversion, sourceP0_shift,
      shiftSequence] using
      (le_refl (NormalPathC2IncrementVariableSpeed.c2ConstVar
        (sourceP0 D (L.N + n)) (wideP1 D MA0 (L.N + n))
        (analyticKhat D) (wideG1 D MA0 NA0 (L.N + n))
        (wideCgWithKhat D (analyticKhat D) MA0 NA0 (L.N + n))))
  · intro n
    rfl
  · exact hbasePhysical
  · exact hdirection L.N
  · simpa using hwidth L.N

end ConfiguredRecursiveSourceP0MergedAssembly
