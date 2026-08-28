import UnitTangentIterates.ConfiguredBaseProfiledSourceFamily
import UnitTangentIterates.ConfiguredRecursiveSourceP0BaseSourceAdapter

/-! # N-aligned configured base sources -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0AlignedBaseSourceFamily

open ConfiguredBaseProfiledSourceFamily
  ConfiguredRecursiveSourceP0BaseSourceAdapter
  ConfiguredRecursiveSourceP0ConstructionCoreProvider
  ConfiguredRecursiveSourceP0ScalarStart
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

/-- The genuine configured source on output `n`, transported to the equally
indexed physical rich stage. -/
def source
    (O : Output MA NA) (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ (ConfiguredBaseProfiledSourceFamily.data O).Hs 0)
    (n : ℕ) :
    MarkingAwareSource
      (((baseProvider O.pair.input O.model_data C
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        hH (kstar_le_analyticKhat (ConfiguredBaseProfiledSourceFamily.data O))).base.step.richStage
          n).stage.increment)
      (ConfiguredRecursiveSourceP0.sourceP0
        (ConfiguredBaseProfiledSourceFamily.data O) n)
      sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap
        (ConfiguredBaseProfiledSourceFamily.data O) n) :=
  sourceOfOutput0 O.pair.input O.model_data C hH
    (kstar_le_analyticKhat (ConfiguredBaseProfiledSourceFamily.data O)) n
    (ConfiguredBaseProfiledSourceFamily.sourceFamily O n)

/-- The unconditional n-aligned configured base correlated column. -/
def baseCorrelated
    (O : Output MA NA) (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ (ConfiguredBaseProfiledSourceFamily.data O).Hs 0) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn0
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ O.pair.input O.model_data)
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ O.pair.input O.model_data)
      (ConfiguredDiagonalStableRowDefectProvider.error
        (ConfiguredBaseProfiledSourceFamily.data O)
        (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff
          (ConfiguredBaseProfiledSourceFamily.data O))) 0
      (ConfiguredRecursiveSourceP0.sourceP0
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredRowCeilingPolynomialEnvelopes.wideP1
        (ConfiguredBaseProfiledSourceFamily.data O) MA0)
      (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredRowCeilingPolynomialEnvelopes.wideG1
        (ConfiguredBaseProfiledSourceFamily.data O) MA0 NA0)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideCgWithKhat
        (ConfiguredBaseProfiledSourceFamily.data O)
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
          (ConfiguredBaseProfiledSourceFamily.data O)) MA0 NA0)
      C
      (ConfiguredCanonicalPairSource.commonC
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredCanonicalPairSource.commonDlt
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredEnrichedConstructionCoreProvider.period
        (ConfiguredBaseProfiledSourceFamily.data O))
      (ConfiguredEnrichedConstructionCoreProvider.diagonal
        (ConfiguredBaseProfiledSourceFamily.data O))
      (fun _ ↦ sourceKh)
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap
        (ConfiguredBaseProfiledSourceFamily.data O)) K0 K1 K2 :=
  ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated0
    O.pair.input O.model_data C hH
    (kstar_le_analyticKhat (ConfiguredBaseProfiledSourceFamily.data O))
    (fun _ ↦ sourceKh)
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap
      (ConfiguredBaseProfiledSourceFamily.data O))
    (source O C hH)

end ConfiguredRecursiveSourceP0AlignedBaseSourceFamily
