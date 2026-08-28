import UnitTangentIterates.ConfiguredGaugeFirstPhysicalSequence
import UnitTangentIterates.ConfiguredRowCeilingPolynomialEnvelopes
import UnitTangentIterates.ConfiguredPolynomialDiagonalStableRowDefectProvider
import UnitTangentIterates.RichStageBoundMonotonicity
import UnitTangentIterates.EnrichedPhysicalChosenRichFamily

/-!
# Gauge-first base column at the physical diagonal error

The gauge-first carrier constructor initially exposes the sharper cost
`rowDefect`.  Physical arclength components require the larger source
`(2 H_n) rowDefect`.  After the large-separation shift has made `H_0 >= 1`,
this module performs that honest weakening and simultaneously widens the
three variable-speed ceilings used by mapped columns.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredGaugeFirstPhysicalDiagonalBase

open ConfiguredGaugeFirstPhysicalSequence
  ConfiguredApproximateDefectPathRowwise
  ConfiguredRichMapStageProvider
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily

def provider
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      MarkedSpace.perim (Q n) = 2 * D.Hs n ∧
      MarkedSpace.ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA NA : ℝ}
    (hH : 1 ≤ D.Hs 0) :
    BaseStageProvider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA) (fun _ => D.kstar)
      (wideG1 D MA NA) (wideCg D MA NA) C c dlt := by
  let B := ConfiguredGaugeFirstPhysicalSequence.provider S hQ 1 C
  apply B.monoBounds
  · intro n
    rw [← D.model_kstar]
    exact ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model |>.le
  · intro n
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
  · intro n
    exact le_max_left _ _
  · intro n
    exact le_max_left _ _
  · intro n
    exact le_max_left _ _

/-- Enrich only the base column actually selected from the aligned provider.
No certificate is requested for arbitrary raw stages. -/
def enrichedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    (hperiod : ∀ n, 1 ≤ period n 0)
    (hnonnegative : ∀ n,
      (PhysicalArclengthJacobiTransition.components (period n 0)
        ((Classical.choice B.base).richStage n).stage.increment.eta).Nonnegative)
    (hbound : ∀ n,
      ComponentBound
        (PhysicalArclengthJacobiTransition.components (period n 0)
          ((Classical.choice B.base).richStage n).stage.increment.eta)
        (diagonal n))
    (hgauge : ∀ n, GaugeCertificate (Classical.choice B.base) n) :
    EnrichedPhysicalChosenRichFamily.BaseProvider Q e
      P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate :=
  ⟨{
    step := Classical.choice B.base
    period_ge_one := hperiod
    components_nonnegative := hnonnegative
    components_bound := by simpa using hbound
    gauge := hgauge }⟩

end ConfiguredGaugeFirstPhysicalDiagonalBase
