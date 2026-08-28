import UnitTangentIterates.ConfiguredCorrelatedConstructionCoreProvider
import UnitTangentIterates.VariableSpeedAnalyticCeilingMonotonicity

/-!
# Configured correlated construction with an independent analytic ceiling

Canonical model interpolation continues to use `D.kstar`.  The selected
recursive columns are widened to a separate constant `khat`, and the exact
correlated analytic sources are retained through the recursive core.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredAnalyticKhatConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyCorrelatedPhysicalCore
  FiniteSmoothRearFamilyCorrelatedRecursion
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider

/-- The exact gauge-first base column widened from canonical `D.kstar` to the
recursive analytic ceiling. -/
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
      (rowP0 D) (wideP1 D MA) (fun _ => khat)
      (wideG1 D MA NA) (wideCgWithKhat D khat MA NA) C c dlt := by
  let raw : ∀ n, RichStageData
      (alignedQ S hQ n) (alignedQ S hQ (n + 1)) (movedRear S hQ n)
      (ConfiguredRowDefectProvider.error D 1 n 0)
      (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n)
      c (C n) dlt :=
    fun n => Classical.choose (exists_richStage S hQ 1 C n)
  refine
    { next := movedRear S hQ
      richStage := fun n => (raw n).monoAnalytic
        (rowP1_nonneg D n) D.kstar_nonneg ?_ (le_max_left _ _) hkhat
        (le_max_left _ _) (le_max_left _ _) }
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

/-- Enriched base provider belonging to the same widened base-column choice. -/
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
    EnrichedPhysicalChosenRichFamily.BaseProvider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D)
      (GaugeFamily (period D) K0 K1 K2) := by
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
    let R := Classical.choose (exists_richStage S hQ 1 C n)
    have hspec := Classical.choose_spec (exists_richStage S hQ 1 C n)
    have hP : 1 ≤ 2 * D.Hs n := by
      have := hH.trans (D.separation_lower n)
      linarith
    have hcost : NormalPath.cost R.stage.increment ≤ rowDefect D n := by
      simpa [ConfiguredRowDefectProvider.error,
        PathMetric.WeightedRecursiveDefect.pullbackError] using
        R.stage.increment_cost
    have H := ComponentBound.of_cost R.stage.increment hspec.2.1
      hspec.2.2 hP hcost
    simpa [step, baseColumnStep, period, diagonal, physicalDefect,
      physicalCoeff, R] using H
  · intro n
    apply GaugeCertificate.base
    refine
      { terminalBase := (step.richStage n).terminalBase
        terminalBase_eq := rfl
        terminalPhysical := ?_ }
    let P := Classical.choice
      (ConfiguredGaugeFirstTerminalPhysicalFacts.chosenTerminalPhysical
        S hQ 1 C n)
    simpa [step, baseColumnStep] using P

/-- The exact depth-zero physical edge belongs to the same gauge-first choice
used by the widened enriched base provider. -/
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
  simpa [baseProvider, baseColumnStep] using
    (ConfiguredGaugeFirstPhysicalSequence.retainedPhysical
      S hQ 1 C n)

/-- Attach analytic sources to the widened exact base column. -/
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
    (source : ∀ n, Source
      (((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n)) :
    CorrelatedColumn (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (rowP0 D) (wideP1 D MA0) (fun _ => khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base
  source := source

/-- Callback-free correlated core with the independent analytic ceiling. -/
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
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (source : ∀ n, Source
      (((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n))
    (G : FiniteSmoothRearFamilyCorrelatedRecursion.Provider
      (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2) :
    FiniteSmoothRearFamilyCorrelatedPhysicalCore.ConstructionCore
      (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)
  base := baseCorrelated S hQ C hH hkhat khRow Qmax source
  provider := G

end ConfiguredAnalyticKhatConstructionCoreProvider
