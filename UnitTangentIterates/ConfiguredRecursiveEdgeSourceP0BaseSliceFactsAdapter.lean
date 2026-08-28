import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSliceFactsPhaseRigid
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter
import UnitTangentIterates.ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily

/-!
# Exact slice facts for the normalized edge base source
-/

noncomputable section

open MarkedSpace

namespace ConfiguredRecursiveEdgeSourceP0BaseSliceFactsAdapter

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily

/-- Transport exact slice facts through the precise phase/rigid normalization
used by `ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput`. -/
def sourceOfOutputSliceFacts
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh0 c dlt kh khat Qmax : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh0 c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ D.Hs 0) (hkhat : D.kstar ≤ khat) (n : ℕ)
    (U : MarkingAwareSource
      (ConfiguredGaugeFirstPhysicalSequence.output S hQ (n + 1)).increment
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D n) kh khat Qmax)
    (H : AnalyticSuccessorSliceFacts U) :
    AnalyticSuccessorSliceFacts
      (ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        S hQ C hH hkhat n U) := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations S hQ (n + 1)
  simpa [ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput, A] using
    H.phaseRigid U A.phase A.translation A.rotation A.rotation_norm

/-- The exact base-slice facts for the configured edge source after the
normalization used by the edge construction core. -/
def edgeTransportedSliceFacts
    {MA NA : ℝ}
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    AnalyticSuccessorSliceFacts
      (ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        O.pair.input O.model_data C O.large.separation_one
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.kstar_le_analyticKhat
          (data O)) n (edgeSourceFamily O n)) :=
  sourceOfOutputSliceFacts O.pair.input O.model_data C
    O.large.separation_one
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.kstar_le_analyticKhat
      (data O)) n (edgeSourceFamily O n) (edgeSliceFacts O n)

end ConfiguredRecursiveEdgeSourceP0BaseSliceFactsAdapter
