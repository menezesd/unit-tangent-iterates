import UnitTangentIterates.ConfiguredRecursiveSourceP0ConstructionCoreProvider
import UnitTangentIterates.ConfiguredBaseInterpolationMarkingAwareSourceResidual
import UnitTangentIterates.MarkingAwareSourcePhaseRigidTransport

/-! # Transport configured base sources into the selected base column -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0BaseSourceAdapter

open ConfiguredRecursiveSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource

/-- N-aligned transport from configured output `n` to configured rich stage
`n`.  This is the sound base adapter for `CorrelatedColumn0`. -/
def sourceOfOutput0
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
      (ConfiguredGaugeFirstPhysicalSequence.output S hQ n).increment
      (sourceP0 D n) kh khat Qmax) :
    MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage n).stage.increment)
      (sourceP0 D n) kh khat Qmax := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := S) (hQ := hQ) n
  let V := U.phaseRigid A.phase A.translation A.rotation A.rotation_norm
  simpa [ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseColumnStep,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
    ConfiguredGaugeFirstPhysicalSequence.richStage,
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData.monoAnalytic,
    RichStageDataPhaseRigidTransport.transportOutput, A, V] using V

/-- A source on the retained interpolation output transports to the exact
phase/rigid-transformed increment selected by the configured base column. -/
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
      (sourceP0 D n) kh khat Qmax) :
    MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (sourceP0 D n) kh khat Qmax := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := S) (hQ := hQ) (n + 1)
  let V := U.phaseRigid A.phase A.translation A.rotation A.rotation_norm
  simpa [ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseColumnStep,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
    ConfiguredGaugeFirstPhysicalSequence.richStage,
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData.monoAnalytic,
    RichStageDataPhaseRigidTransport.transportOutput, A, V] using V

/-- Rowwise form of `sourceOfOutput`, matching the source family expected by
the recursive construction core. -/
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
      (sourceP0 D n) (khRow n) khat (Qmax n)) :
    ∀ n, MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (sourceP0 D n) (khRow n) khat (Qmax n) :=
  fun n => sourceOfOutput S hQ C hH hkhat n (U n)

/-- A residual source constructed on the retained interpolation output becomes
the source of the exact phase/rigid-transformed next-row increment selected by
the configured base column. -/
def sourceOfResidual
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh0 c dlt kh khat Qmax : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh0 c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ D.Hs 0) (hkhat : D.kstar ≤ khat) (n : ℕ)
    (R : ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual
      (ConfiguredGaugeFirstPhysicalSequence.output S hQ (n + 1))
      (sourceP0 D n) kh khat Qmax)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (hkh : H.k0 ≤ kh) :
    MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (sourceP0 D n) kh khat Qmax := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := S) (hQ := hQ) (n + 1)
  let W := ConfiguredGaugeFirstPhysicalSequence.output S hQ (n + 1)
  let U := ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual
    W (sourceP0 D n) kh khat Qmax R H hkh
  exact sourceOfOutput S hQ C hH hkhat n U

end ConfiguredRecursiveSourceP0BaseSourceAdapter
