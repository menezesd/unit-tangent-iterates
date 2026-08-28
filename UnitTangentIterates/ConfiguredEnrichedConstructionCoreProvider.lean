import UnitTangentIterates.ConfiguredGaugeFirstPhysicalDiagonalBase
import UnitTangentIterates.ConfiguredGaugeFirstTerminalPhysicalFacts
import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedMapProvider
import UnitTangentIterates.EnrichedPhysicalConstructionCore

/-!
# Configured enriched construction-core provider

This is the base-side counterpart of the deterministic enriched rear-family
map provider.  It selects the gauge-first physical diagonal once, equips that
same choice with physical arclength component bounds and its ordinary terminal
certificate, and packages it with the deterministic mapped-column provider.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredEnrichedConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider

/-- Physical perimeter of a stage in row `n`.  Rear transport decreases the
model level together with the row, so this is independent of the depth. -/
def period (D : ConstructedConfiguredSequenceWeighted.Data) : ℕ → ℕ → ℝ :=
  fun n _ => 2 * D.Hs n

/-- The honest diagonal component source. -/
def diagonal (D : ConstructedConfiguredSequenceWeighted.Data) : ℕ → ℝ :=
  physicalDefect D

/-- The exact selected gauge-first base stage, weakened to the physical
diagonal error and the mapped-column derivative ceilings without making a
second choice. -/
def baseColumnStep
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA NA : ℝ} (hH : 1 ≤ D.Hs 0) :
    ColumnStep (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      0
      (rowP0 D) (wideP1 D MA) (fun _ => D.kstar)
      (wideG1 D MA NA) (wideCg D MA NA) C c dlt := by
  let raw : ∀ n, RichStageData
      (alignedQ S hQ n) (alignedQ S hQ (n + 1)) (movedRear S hQ n)
      (ConfiguredRowDefectProvider.error D 1 n 0)
      (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n)
      c (C n) dlt :=
    fun n => Classical.choose (exists_richStage S hQ 1 C n)
  let step : ColumnStep (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (rowP0 D) (wideP1 D MA) (fun _ => D.kstar)
      (wideG1 D MA NA) (wideCg D MA NA) C c dlt :=
    { next := movedRear S hQ
      richStage := fun n => (raw n).monoBounds
        (by
          rw [← D.model_kstar]
          exact ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model |>.le)
        (by
          have hHn : 1 ≤ 2 * D.Hs n := by
            have := hH.trans (D.separation_lower n)
            linarith
          have hdef0 := (ConfiguredStableRowDefectProvider.provider D).nonnegative n 0
          simpa [ConfiguredRowDefectProvider.error,
            ConfiguredStableRowDefectProvider.error,
            ConfiguredDiagonalStableRowDefectProvider.error,
            PathMetric.WeightedRecursiveDefect.pullbackError,
            physicalCoeff, Nat.add_zero] using
            (mul_le_mul_of_nonneg_right hHn hdef0))
        (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) }
  exact step

/-- Plain provider projection of the exact base column. -/
def baseStageProvider
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA NA : ℝ} (hH : 1 ≤ D.Hs 0) :
    BaseStageProvider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA) (fun _ => D.kstar)
      (wideG1 D MA NA) (wideCg D MA NA) C c dlt :=
  ⟨⟨baseColumnStep S hQ C hH⟩⟩

/-- The base column selected above, enriched with the physical component and
ordinary terminal certificates belonging to that exact selection. -/
def baseProvider
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0) :
    EnrichedPhysicalChosenRichFamily.BaseProvider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D)
      (GaugeFamily (period D) K0 K1 K2) := by
  let step := baseColumnStep S hQ C (MA := MA0) (NA := NA0) hH
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
    have hcost : PathMetric.NormalPath.cost R.stage.increment ≤ rowDefect D n := by
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

/-- Aggregate the configured diagonal provider and deterministic enriched map
provider into the callback-free recursive construction core. -/
def constructionCore
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (G : Provider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2) :
    EnrichedPhysicalChosenRichFamily.ConstructionCore (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) (GaugeFamily (period D) K0 K1 K2)
      a MA NA K0 K1 K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)
  baseProvider := baseProvider S hQ C hH
  mapProvider := FiniteSmoothRearFamilyEnrichedMapProvider.mapProvider G

end ConfiguredEnrichedConstructionCoreProvider
