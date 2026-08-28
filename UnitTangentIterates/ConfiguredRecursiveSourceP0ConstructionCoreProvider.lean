import UnitTangentIterates.ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider
import UnitTangentIterates.ConfiguredRecursiveSourceP0

/-!
# Configured marking-aware core with the recursive speed floor

The configured base interpolation is initially certified with `rowP0`.  The
recursive selected-rear estimates require the smaller polynomial floor
`sourceP0`.  Since `P0` occurs only as a denominator in upper estimates, the
existing monotonicity theorem lowers the certificate without changing any
selected path, marking, component, or physical endpoint datum.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0ConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredRecursiveSourceP0
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider

/-- Lower only the speed-floor parameter stored by a rich stage. -/
def lowerRichStageP0
    {p front rear : Data}
    {bound P0 P0' P1 khat G1 Cg c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt)
    (hP0' : 0 < P0') (hle : P0' ≤ P0) :
    RichStageData p front rear bound P0' P1 khat G1 Cg c C dlt where
  stage :=
    { increment := S.stage.increment
      increment_geometry :=
        ConfiguredApproximateDefectPath.IsVariableSpeedNormalPath.mono_P0
          S.stage.increment_geometry hP0' hle
      increment_cost := S.stage.increment_cost
      rear_curve_deriv := S.stage.rear_curve_deriv
      rear_vel_deriv := S.stage.rear_vel_deriv
      rear_periodic := S.stage.rear_periodic
      rear_curvature_nonnegative := S.stage.rear_curvature_nonnegative
      range_edge := S.stage.range_edge
      rear_harnack := S.stage.rear_harnack }
  terminalBase := S.terminalBase
  lambda := S.lambda
  Lambda := S.Lambda
  marking := S.marking

/-- The exact configured base step, with its certificate weakened from
`rowP0` to the recursive floor `sourceP0`. -/
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
      (sourceP0 D) (wideP1 D MA) (fun _ ↦ khat)
      (wideG1 D MA NA) (wideCgWithKhat D khat MA NA) C c dlt := by
  let raw := fun n ↦
    ConfiguredGaugeFirstPhysicalSequence.richStage S hQ 1 C n
  refine
    { next := movedRear S hQ
      richStage := fun n ↦ lowerRichStageP0
        ((raw n).monoAnalytic
          (rowP1_nonneg D n) D.kstar_nonneg ?_ (le_max_left _ _) hkhat
          (le_max_left _ _) (le_max_left _ _))
        (sourceP0_pos D n) (sourceP0_le_rowP0 D n) }
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

/-- The enriched base provider at the recursive speed floor. -/
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
      (sourceP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
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
    simpa [step, baseColumnStep, lowerRichStageP0, period, diagonal,
      physicalDefect, physicalCoeff, R] using H
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
      simpa [step, baseColumnStep, lowerRichStageP0, A, r] using heq]
    exact ConfiguredGaugeFirstTerminalPhysicalFacts.moveFacts
      (ConfiguredGaugeFirstTerminalPhysicalFacts.carrierFacts (S.carrier n))
      A.translation A.rotation r A.rotation_norm

/-- The same selected base column equipped with genuine nonaffine sources. -/
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
      (sourceP0 D n) (khRow n) khat (Qmax n)) :
    CorrelatedColumn (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (sourceP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base
  source := source

/-- The configured base column with its source attached to the physical stage
at the same index.  Unlike `baseCorrelated`, this consumes `richStage n` and
therefore has no hidden successor-edge shift. -/
def baseCorrelated0
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
          n).stage.increment)
      (sourceP0 D n) (khRow n) khat (Qmax n)) :
    CorrelatedColumn0 (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (sourceP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base
  source := source

/-- Sound configured construction core at the recursive speed floor. -/
def constructionCore
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat)
    (khRow Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (source : ∀ n, MarkingAwareSource
      (((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (sourceP0 D n) (khRow n) khat (Qmax n))
    (G : Provider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (sourceP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax a MA NA K0 K1 K2) :
    ConstructionCore (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (sourceP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax a MA NA K0 K1 K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)
  base := baseCorrelated S hQ C hH hkhat khRow Qmax source
  provider := G

/-- The physical base edge is unchanged by lowering the analytic speed floor. -/
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
        simpa [baseProvider, baseColumnStep, lowerRichStageP0, A, r] using heq]
  rw [hnext]
  exact ⟨P⟩

end ConfiguredRecursiveSourceP0ConstructionCoreProvider
