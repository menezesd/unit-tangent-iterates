import UnitTangentIterates.ConfiguredApproximateDefectPathActualTerminal
import UnitTangentIterates.ConfiguredRowDefectProvider

/-!
# Configured rich base-stage provider

This adapter turns the actual terminal of the configured interpolation flow
into the depth-zero rich column.  Tube membership of the terminal itself is
not assumed here; it is deferred to the simultaneous row-budget argument.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRichBaseStageProvider

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  GaugeRearFamilyVariableTerminal

/-- Physical normalization of the reconstructed `kH` carrier.  The carrier
may be shifted to anchor the actual flow marking.  Range and Harnack are
therefore stated for every such shift. -/
structure PhysicalRearNormalization
    (D : ConstructedConfiguredSequenceWeighted.Data) (Q : ℕ → Data) where
  carrier : ∀ n, RearCarrier D n
  range_shift : ∀ n b,
    range (⇑(Q (n + 1)).1) =
      range (UnitTangent.unitTangentMap
        (ev (MarkedShift.shiftData b (carrier n).data)))
  strictness_shift : ∀ n b,
    UnconditionalAssembly.LimitStrictnessDataH
      (MarkedShift.shiftData b (carrier n).data)

/-- The depth-zero configured interpolation stages, with the exact honest
row defect and the actual nonaffine terminal markings. -/
def provider
    (D : ConstructedConfiguredSequenceWeighted.Data) {K c dlt : ℝ}
    {Q : ℕ → Data}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (R : PhysicalRearNormalization D Q)
    (C : ℕ → ℝ) :
    BaseStageProvider Q (ConfiguredRowDefectProvider.error D K)
      (rowP0 D) (rowP1 D) (fun _ ↦ D.kstar) (rowG1 D) (rowCg D) C c dlt := by
  let O : ∀ n, Output D Q n (R.carrier n) := fun n =>
    Classical.choice (exists_output D hQ n (R.carrier n))
  let S : ∀ n,
      RichStageData (Q n) (Q (n + 1)) (O n).rear
        (ConfiguredRowDefectProvider.error D K n 0)
        (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n)
        c (C n) dlt := fun n => by
    let A := R.carrier n
    let W := O n
    have hbase : IsTubeMember A.c 0 A.dlt W.terminalBase := by
      rw [W.terminalBase_eq]
      exact MarkedShift.isTubeMember_shiftData A.tube W.baseShift
    have hcont : Continuous W.marking.marking.psi :=
      continuous_iff_continuousAt.2 fun u =>
        (W.marking.psi_deriv u).continuousAt
    have hmono : StrictMono W.marking.marking.psi := by
      refine strictMono_of_deriv_pos fun u => ?_
      rw [(W.marking.psi_deriv u).deriv]
      exact lt_of_lt_of_le W.marking.lambda_pos
        (W.marking.marking.lower u)
    have hsurj : Surjective W.marking.marking.psi :=
      GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
        one_pos hcont hmono W.marking.marking.translate W.marking.psi_zero
    have hres : RawTerminalResidual (Q (n + 1)) W.rear :=
      rawTerminalResidual_of_orientedReparametrization
        A.c_pos A.dlt_pos W.marking.lambda_pos hbase W.marking.marking
        W.rear_curve_deriv W.rear_vel_deriv W.rear_curvature_nonnegative
        hsurj (by
          rw [W.terminalBase_eq]
          exact R.range_shift n W.baseShift)
        (by
          rw [W.terminalBase_eq]
          exact R.strictness_shift n W.baseShift)
    have hraw : RawStageOutput (Q n) (Q (n + 1)) W.rear
        (ConfiguredRowDefectProvider.error D K n 0)
        (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n) :=
      { increment := W.increment
        increment_geometry := W.increment_geometry
        increment_cost := by
          simpa [ConfiguredRowDefectProvider.error,
            PathMetric.WeightedRecursiveDefect.pullbackError] using
              W.increment_cost
        rear_curve_deriv := hres.rear_curve_deriv
        rear_vel_deriv := hres.rear_vel_deriv
        rear_periodic := hres.rear_periodic
        rear_curvature_nonnegative := hres.rear_curvature_nonnegative
        range_edge := hres.range_edge
        rear_harnack := hres.rear_harnack }
    exact
      { stage := hraw
        terminalBase := W.terminalBase
        lambda := W.lambda
        Lambda := W.Lambda
        marking := W.marking }
  exact ⟨⟨{
    next := fun n => (O n).rear
    richStage := S }⟩⟩

/-- Enlarge the three upper row ceilings without changing the honest
interpolation endpoint, defect, or normalized marking.  This is the base-side
adapter used when the common recursive ceilings are chosen large enough for
the anchored rear-family transport. -/
def provider_mono
    (D : ConstructedConfiguredSequenceWeighted.Data) {K c dlt : ℝ}
    {Q : ℕ → Data}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (R : PhysicalRearNormalization D Q)
    (C P1 G1 Cg : ℕ → ℝ)
    (hP1 : ∀ n, rowP1 D n ≤ P1 n)
    (hG1 : ∀ n, rowG1 D n ≤ G1 n)
    (hCg : ∀ n, rowCg D n ≤ Cg n)
    (hkstar : 0 ≤ D.kstar) :
    BaseStageProvider Q (ConfiguredRowDefectProvider.error D K)
      (rowP0 D) P1 (fun _ ↦ D.kstar) G1 Cg C c dlt := by
  let B := Classical.choice
    (provider (K := K) (c := c) (dlt := dlt) D hQ R C).base
  refine ⟨⟨{
    next := B.next
    richStage := fun n => ?_ }⟩⟩
  let S := B.richStage n
  exact
    { stage :=
        { increment := S.stage.increment
          increment_geometry :=
            NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath.mono
              S.stage.increment S.stage.increment_geometry hkstar
              (hP1 n) (hG1 n) (hCg n)
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
      marking := S.marking }

end ConfiguredRichBaseStageProvider
