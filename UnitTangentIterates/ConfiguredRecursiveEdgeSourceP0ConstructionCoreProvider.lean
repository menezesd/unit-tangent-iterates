import UnitTangentIterates.ConfiguredRecursiveSourceP0ConstructionCoreProvider
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth

/-! # Configured construction core at the genuine successor-edge floor -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRowCeilingPolynomialEnvelopes
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

def baseColumnStep
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA NA : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) :
    ColumnStep (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (edgeSourceP0 D) (edgeP1 D MA) (fun _ ↦ khat)
      (edgeG1 D MA NA) (edgeCgWithKhat D khat MA NA) C c dlt := by
  let raw := fun n ↦ ConfiguredGaugeFirstPhysicalSequence.richStage S hQ 1 C n
  refine
    { next := movedRear S hQ
      richStage := fun n ↦
        ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0
          ((raw n).monoAnalytic
            (rowP1_nonneg D n) D.kstar_nonneg ?_
            (((le_max_left _ _).trans (le_max_left _ _)).trans
              (le_max_left _ _)) hkhat
            (((le_max_left _ _).trans (le_max_left _ _)).trans
              (le_max_left _ _))
            (((le_max_left _ _).trans (le_max_left _ _)).trans
              (le_max_left _ _)))
          (edgeSourceP0_pos D n) (edgeSourceP0_le_rowP0 D n) }
  have hHn : 1 ≤ 2 * D.Hs n := by
    have := hH.trans (D.separation_lower n)
    linarith
  have hdef0 := (ConfiguredStableRowDefectProvider.provider D).nonnegative n 0
  simpa [ConfiguredRowDefectProvider.error,
    ConfiguredStableRowDefectProvider.error,
    ConfiguredDiagonalStableRowDefectProvider.error,
    PathMetric.WeightedRecursiveDefect.pullbackError,
    physicalCoeff, Nat.add_zero] using
    (mul_le_mul_of_nonneg_right hHn hdef0)

def baseProvider
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) :
    BaseProvider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (edgeSourceP0 D) (edgeP1 D MA0) (fun _ ↦ khat)
      (edgeG1 D MA0 NA0) (edgeCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) (GaugeFamily (period D) K0 K1 K2) := by
  let step := baseColumnStep S hQ C (MA := MA0) (NA := NA0) hH hkhat
  refine ⟨{
    step := step
    period_ge_one := ?_
    components_nonnegative := ?_
    components_bound := ?_
    gauge := ?_ }⟩
  · intro n
    change 1 ≤ 2 * D.Hs n
    have := hH.trans (D.separation_lower n)
    linarith
  · intro n
    apply PhysicalArclengthJacobiTransition.components_nonnegative
    exact mul_pos (by norm_num) (D.model.separation_pos n)
  · intro n
    let R := ConfiguredGaugeFirstPhysicalSequence.richStage S hQ 1 C n
    have hspec := ConfiguredGaugeFirstPhysicalSequence.richStage_spec S hQ 1 C n
    have hP : 1 ≤ 2 * D.Hs n := by
      have := hH.trans (D.separation_lower n)
      linarith
    have hcost : NormalPath.cost R.stage.increment ≤ rowDefect D n := by
      simpa [ConfiguredRowDefectProvider.error,
        PathMetric.WeightedRecursiveDefect.pullbackError] using
        R.stage.increment_cost
    have H := ComponentBound.of_cost R.stage.increment hspec.2.1
      hspec.2.2 hP hcost
    simpa [step, baseColumnStep,
      ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
      period, diagonal, physicalDefect, physicalCoeff, R] using H
  · intro n
    apply GaugeCertificate.base
    refine
      { terminalBase := (step.richStage n).terminalBase
        terminalBase_eq := rfl
        terminalPhysical := ?_ }
    let A := presentations (S := S) (hQ := hQ) n
    let r := rearPhase S hQ A
    have heq := (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
      S hQ 1 C n).1
    rw [show (step.richStage n).terminalBase =
        RichStageDataPhaseRigidTransport.move
          A.translation A.rotation r (S.carrier n).data by
      simpa [step, baseColumnStep,
        ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
        A, r] using heq]
    exact ConfiguredGaugeFirstTerminalPhysicalFacts.moveFacts
      (ConfiguredGaugeFirstTerminalPhysicalFacts.carrierFacts (S.carrier n))
      A.translation A.rotation r A.rotation_norm

def baseCorrelated
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, MarkingAwareSource
      (((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (edgeSourceP0 D n) (khRow n) khat (Qmax n)) :
    CorrelatedColumn (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (edgeSourceP0 D) (edgeP1 D MA0) (fun _ ↦ khat)
      (edgeG1 D MA0 NA0) (edgeCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base
  source := source

theorem basePhysical
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics kh
      ((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage n).terminalBase
      (alignedQ S hQ (n + 1))) := by
  let A := presentations (S := S) (hQ := hQ) n
  let r := rearPhase S hQ A
  let P := Nonempty.some (physicalStep S A r)
  have heq := (ConfiguredGaugeFirstPhysicalSequence.richStage_spec S hQ 1 C n).1
  have hnext : alignedQ S hQ (n + 1) = (next S A r).data := by
    simp [alignedQ, presentations, A, r, rearPhase]
  rw [show ((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage n).terminalBase =
      RichStageDataPhaseRigidTransport.move
        A.translation A.rotation r (S.carrier n).data by
        simpa [baseProvider, baseColumnStep,
          ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
          A, r] using heq]
  rw [hnext]
  exact ⟨P⟩

end ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider
