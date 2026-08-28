import Mathlib
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.GaugeControlledClosingConfiguredModel
import UnitTangentIterates.ControlledJunctionVariableSpeedDistance

noncomputable section

open Set Filter Function Topology MarkedSpace MainTheoremConditional

namespace PathMetric

open NormalPath

/-- Summable controlled junctions, retaining the quantitative distance from
every stage to the limit.  This is the tail estimate omitted by the original
projection `exists_limit_of_summable_controlledJunctions`. -/
theorem exists_limit_of_summable_controlledJunctions_tail
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt Cmetric : ℝ}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * cost (S.path n))
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Tendsto Q atTop (𝓝 X) → IsTubeMember c kmin dlt X) :
    ∃ X : Data,
      Tendsto Q atTop (𝓝 X) ∧ IsTubeMember c kmin dlt X ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) ∧
      (∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * e n) ∧
      (∀ N, dist (Q N) X ≤ Cmetric * ShadowingTails.tail e N) := by
  have hstep : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * e n := by
    intro n
    exact (hdist n).trans (mul_le_mul_of_nonneg_left (hcost n) hCmetric)
  obtain ⟨X, hX, htail⟩ :=
    ShadowingTails.exists_limit_of_summable_increments hesum hstep
  exact ⟨X, hX, htube_closed X hX, fun n => ⟨S.path_c2 n⟩, hcost, hstep, htail⟩

/-- Transport variant of the tail-retaining controlled-junction limit. -/
theorem exists_limit_of_summable_controlledJunctions_transport_tail
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt Cmetric : ℝ} {B : Data → Data}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * cost (S.path n))
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Tendsto Q atTop (𝓝 X) → IsTubeMember c kmin dlt X)
    (htransport : ∀ n, Q n = B (Q (n + 1))) (hB : Continuous B) :
    ∃ X : Data,
      Tendsto Q atTop (𝓝 X) ∧ IsTubeMember c kmin dlt X ∧ X = B X ∧
      (∀ n, Q n = B (Q (n + 1))) ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) ∧
      (∀ N, dist (Q N) X ≤ Cmetric * ShadowingTails.tail e N) := by
  obtain ⟨X, hX, hXtube, hC2, hcost', -, htail⟩ :=
    exists_limit_of_summable_controlledJunctions_tail S he0 hesum hcost hCmetric
      hdist htube htube_closed
  have hshift : Tendsto (fun n => Q (n + 1)) atTop (𝓝 X) :=
    hX.comp (tendsto_add_atTop_nat 1)
  have hBX : Tendsto (fun n => B (Q (n + 1))) atTop (𝓝 (B X)) :=
    hB.continuousAt.tendsto.comp hshift
  have hsame : Tendsto (fun n => B (Q (n + 1))) atTop (𝓝 X) := by
    have hfun : (fun n => B (Q (n + 1))) = Q := funext fun n => (htransport n).symm
    rw [hfun]
    exact hX
  exact ⟨X, hX, hXtube, tendsto_nhds_unique hsame hBX, htransport,
    hC2, hcost', htail⟩

/-- The zeroth sequence of a gauge-controlled family automatically supplies
the initial closing tail certificate once its standard endpoint metric
estimate is instantiated. -/
def GaugeControlledFamily.initialTailBound
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg Cmetric : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ k, dist (Q 0 k) (Q 0 (k + 1)) ≤
      Cmetric * cost ((G.sequence 0).path k))
    :
    ControlledJunctionInitialTailBound Q
      (Cmetric * ShadowingTails.tail (G.error 0) 0) where
  nonneg := mul_nonneg hCmetric (ShadowingTails.tail_nonneg (G.error_nonneg 0) 0)
  limit_dist := by
    intro X hX
    have hstep : ∀ k, dist (Q 0 k) (Q 0 (k + 1)) ≤ Cmetric * G.error 0 k := by
      intro k
      exact (hdist k).trans
        (mul_le_mul_of_nonneg_left (G.path_cost 0 k) hCmetric)
    obtain ⟨Y, hY, htail⟩ := ShadowingTails.exists_limit_of_summable_increments
      (G.error_summable 0) hstep
    have hYX : Y = X 0 := tendsto_nhds_unique hY (hX 0)
    simpa [hYX, dist_comm] using htail 0

/-- Variable-speed gauge families discharge their endpoint metric estimate
from tube membership and the stored variable-speed certificates. -/
def GaugeControlledFamily.initialTailBound_ofVariableSpeed
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg c kmin dlt : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (htube : ∀ n k, IsTubeMember c kmin dlt (Q n k))
    :
    ControlledJunctionInitialTailBound Q
      (NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
        ShadowingTails.tail (G.error 0) 0) :=
  G.initialTailBound hconst
    (controlledJunction_distances_variableSpeed (G.sequence 0) (htube 0)
      (G.variableSpeed 0))

/-- Configured closing data directly from a variable-speed gauge family.  The
shadowing distance is no longer an input: it is the metric constant times the
summable zeroth error tail. -/
def GaugeControlledClosingInputs.ofConfiguredModelFrontGaugeTail
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt P0 P1 khat G1 Cg Cw : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (htube : ∀ n k, IsTubeMember c kmin dlt (Q n k))
    (hrepresentative : ∀ (X : ℕ → Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hmodel : ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I ≤ Cw)
    (hgap : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
          ShadowingTails.tail (G.error 0) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
          ShadowingTails.tail (G.error 0) 0) / Real.pi) :
    GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
      c kmin dlt :=
  GaugeControlledClosingInputs.ofConfiguredModelFrontUniformWidthTail model hc hkmin hdlt
    htube hrepresentative htangentRepresentative hRorbit
    (G.initialTailBound_ofVariableSpeed hconst htube) hmodel hmodelPerim hwidth hgap

/-- Nonnegative-tube version of the configured gauge-tail closing bundle. -/
def GaugeControlledClosingInputsNonnegative.ofConfiguredModelFrontGaugeTail
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {c dlt P0 P1 khat G1 Cg Cw : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hc : 0 < c) (hdlt : 0 < dlt)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (hstrict : ∀ (X : ℕ → Data), (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, UnconditionalAssembly.LimitStrictnessData (X n))
    (hrep : ∀ (X : ℕ → Data), (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (ev (X n)) = range (R n))
    (htrep : ∀ (X : ℕ → Data), (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (horbit : ∀ n, range (R (n+1)) = range (UnitTangent.unitTangentMap (R n)))
    (hmodel : ev (Q 0 0) = TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hper : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width (range (TwoCapPairsAssembly.front (kappas 0)
      model.thetaBase (Hs 0))) Complex.I ≤ Cw)
    (hgap : Cw + 2 * (NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
      ShadowingTails.tail (G.error 0) 0) < (2 * Hs 0 -
      NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
        ShadowingTails.tail (G.error 0) 0) / Real.pi) :
    GaugeControlledClosingInputsNonnegative Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) c dlt := by
  let tail := G.initialTailBound_ofVariableSpeed hconst htube
  exact
    { c_pos := hc
      dlt_pos := hdlt
      tube := htube
      limitStrictness := hstrict
      representative := hrep
      tangentRepresentative := htrep
      representativeOrbit := horbit
      modelPeriod := 2 * Hs 0
      distanceError := _
      widthCeiling := Cw
      halfWidthFloor := Hs 0
      widthDirection := Complex.I
      model_continuous := Differentiable.continuous fun s =>
        (TwoCapPairsAssembly.front_hasDerivAt (theta0 := model.thetaBase)
          (H := Hs 0) (model.curvature_continuous 0) s).differentiableAt
      model_periodic := TwoCapPairsAssembly.front_periodic (theta0 := model.thetaBase)
        (H := Hs 0) (model.curvature_continuous 0) (model.curvature_periodic 0)
          (model.total_turning 0)
      modelPeriod_pos := by linarith [model.separation_pos 0]
      widthDirection_unit := by simp
      distanceError_nonneg := tail.nonneg
      model_width := hwidth
      initial_close := tail.initial_close hc htube hmodel
      initial_perimeter_lower := tail.initial_perimeter_lower hper
      width_gap := hgap }

/-- Top-level input package with the entire summable-tail closing estimate
threaded from the gauge family. -/
def PaperControlledJunctionInputs.ofGaugeControlledConfiguredModel
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (C : GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) c kmin dlt) :
    PaperControlledJunctionInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) :=
  PaperControlledJunctionInputs.ofGaugeControlledFamily model G hconst C

/-- Paper capstone from a gauge-controlled configured model after the
variable-speed tail estimate has supplied the closing metric control. -/
theorem paper_main_theorem_of_gaugeControlledConfiguredModel
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (C : GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) c kmin dlt) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L :=
  paper_main_theorem_of_configured_controlledJunctions model
    (PaperControlledJunctionInputs.ofGaugeControlledConfiguredModel model G hconst C)

end PathMetric
