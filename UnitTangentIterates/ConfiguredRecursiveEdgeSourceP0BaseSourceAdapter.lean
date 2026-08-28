import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider
import UnitTangentIterates.MarkingAwareSourcePhaseRigidTransport

/-! # Transport edge-floor sources into the configured base column -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter

open ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource

def sourceOfOutput
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh0 c dlt kh khat Qmax : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh0 c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ D.Hs 0) (hkhat : D.kstar ≤ khat) (n : ℕ)
    (U : MarkingAwareSource
      (ConfiguredGaugeFirstPhysicalSequence.output S hQ (n + 1)).increment
      (edgeSourceP0 D n) kh khat Qmax) :
    MarkingAwareSource
      (((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (edgeSourceP0 D n) kh khat Qmax := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := S) (hQ := hQ) (n + 1)
  let V := U.phaseRigid A.phase A.translation A.rotation A.rotation_norm
  simpa [ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseColumnStep,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
    ConfiguredGaugeFirstPhysicalSequence.richStage,
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData.monoAnalytic,
    RichStageDataPhaseRigidTransport.transportOutput, A, V] using V

def sourcesOfOutputs
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh0 c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh0 c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ D.Hs 0) (hkhat : D.kstar ≤ khat)
    (khRow Qmax : ℕ → ℝ)
    (U : ∀ n, MarkingAwareSource
      (ConfiguredGaugeFirstPhysicalSequence.output S hQ (n + 1)).increment
      (edgeSourceP0 D n) (khRow n) khat (Qmax n)) :
    ∀ n, MarkingAwareSource
      (((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (edgeSourceP0 D n) (khRow n) khat (Qmax n) :=
  fun n ↦ sourceOfOutput S hQ C hH hkhat n (U n)

end ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter
