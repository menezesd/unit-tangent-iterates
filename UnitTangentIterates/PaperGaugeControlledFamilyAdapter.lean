import Mathlib
import UnitTangentIterates.GaugeControlledJunctionOutput
import UnitTangentIterates.PaperControlledJunctionInputsConstructor
import UnitTangentIterates.PaperMainTheoremControlled

noncomputable section

open Filter Function Set Topology MainTheoremConditional

namespace PathMetric

/-- The non-gauge inputs left after `GaugeControlledFamily` has supplied the
controlled sequences, summable costs, and variable-speed certificates. -/
structure GaugeControlledClosingInputs
    (Q : ℕ → ℕ → MarkedSpace.Data) (R : ℕ → ℝ → ℂ) (M : ℝ → ℂ)
    (c kmin dlt : ℝ) where
  c_pos : 0 < c
  kmin_pos : 0 < kmin
  dlt_pos : 0 < dlt
  tube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k)
  representative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, range (MarkedSpace.ev (X n)) = range (R n)
  tangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
    range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
      range (UnitTangent.unitTangentMap (R n))
  representativeOrbit : ∀ n,
    range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n))
  modelPeriod : ℝ
  distanceError : ℝ
  widthCeiling : ℝ
  halfWidthFloor : ℝ
  widthDirection : ℂ
  model_continuous : Continuous M
  model_periodic : Periodic M modelPeriod
  modelPeriod_pos : 0 < modelPeriod
  widthDirection_unit : ‖widthDirection‖ = 1
  distanceError_nonneg : 0 ≤ distanceError
  model_width : Width.width (range M) widthDirection ≤ widthCeiling
  initial_close : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M) ≤ distanceError
  initial_perimeter_lower : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    2 * halfWidthFloor - distanceError ≤ MarkedSpace.perim (X 0)
  width_gap : widthCeiling + 2 * distanceError <
    (2 * halfWidthFloor - distanceError) / Real.pi

/-- Paper-faithful closing inputs on the closed nonnegative-curvature tube.
Strict ovality is recovered only after passage to the limit. -/
structure GaugeControlledClosingInputsNonnegative
    (Q : ℕ → ℕ → MarkedSpace.Data) (R : ℕ → ℝ → ℂ) (M : ℝ → ℂ)
    (c dlt : ℝ) where
  c_pos : 0 < c
  dlt_pos : 0 < dlt
  tube : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt (Q n k)
  limitStrictness : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, UnconditionalAssembly.LimitStrictnessData (X n)
  representative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, range (MarkedSpace.ev (X n)) = range (R n)
  tangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
    range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
      range (UnitTangent.unitTangentMap (R n))
  representativeOrbit : ∀ n,
    range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n))
  modelPeriod : ℝ
  distanceError : ℝ
  widthCeiling : ℝ
  halfWidthFloor : ℝ
  widthDirection : ℂ
  model_continuous : Continuous M
  model_periodic : Periodic M modelPeriod
  modelPeriod_pos : 0 < modelPeriod
  widthDirection_unit : ‖widthDirection‖ = 1
  distanceError_nonneg : 0 ≤ distanceError
  model_width : Width.width (range M) widthDirection ≤ widthCeiling
  initial_close : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M) ≤ distanceError
  initial_perimeter_lower : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    2 * halfWidthFloor - distanceError ≤ MarkedSpace.perim (X 0)
  width_gap : widthCeiling + 2 * distanceError <
    (2 * halfWidthFloor - distanceError) / Real.pi

/-- Nonnegative-tube gauge constructor. -/
def PaperControlledJunctionInputs.ofGaugeControlledFamilyNonnegative
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (_model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    {c dlt P0 P1 khat G1 Cg : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (C : GaugeControlledClosingInputsNonnegative Q R M c dlt) :
    PaperControlledJunctionInputs Q R M := by
  refine
    { sequence := G.sequence, error := G.error, c := c, kmin := 0, dlt := dlt
      metricConstant := NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg
      error_nonneg := G.error_nonneg, error_summable := G.error_summable
      path_cost := G.path_cost, metricConstant_nonneg := hmetric
      step_distance := fun n => controlledJunction_distances_variableSpeed
        (G.sequence n) (C.tube n) (G.variableSpeed n)
      tube := C.tube, tube_closed := ?_, representative := C.representative
      tangent_representative := C.tangentRepresentative
      representative_orbit := C.representativeOrbit, limit_oval := ?_
      modelPeriod := C.modelPeriod, distanceError := C.distanceError
      widthCeiling := C.widthCeiling, halfWidthFloor := C.halfWidthFloor
      widthDirection := C.widthDirection, model_continuous := C.model_continuous
      model_periodic := C.model_periodic, modelPeriod_pos := C.modelPeriod_pos
      widthDirection_unit := C.widthDirection_unit
      distanceError_nonneg := C.distanceError_nonneg, model_width := C.model_width
      initial_regular := ?_, initial_close := C.initial_close
      initial_perimeter_lower := C.initial_perimeter_lower, width_gap := C.width_gap }
  · intro n X hX
    exact (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto hX
      (Eventually.of_forall (C.tube n))
  · intro X hX n
    have hmem := (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hX n)
      (Eventually.of_forall (C.tube n))
    exact UnconditionalAssembly.isOval_ev_of_limitStrictnessData
      C.c_pos C.dlt_pos hmem (C.limitStrictness X hX n)
  · intro X hX
    have hmem := (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hX 0)
      (Eventually.of_forall (C.tube 0))
    have hov := UnconditionalAssembly.isOval_ev_of_limitStrictnessData
      C.c_pos C.dlt_pos hmem (C.limitStrictness X hX 0)
    exact ⟨hov.continuous, MarkedSpace.perim_pos C.c_pos hmem,
      MarkedSpace.periodic_ev C.c_pos hmem⟩

/-- Smart constructor from the completed gauge half and the remaining
geometric range/closing data. -/
def PaperControlledJunctionInputs.ofGaugeControlledFamily
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (C : GaugeControlledClosingInputs Q R M c kmin dlt) :
    PaperControlledJunctionInputs Q R M :=
  PaperControlledJunctionInputs.ofVariableSpeed model G.sequence G.error
    C.c_pos C.kmin_pos C.dlt_pos G.error_nonneg G.error_summable G.path_cost
    hmetric C.tube G.variableSpeed C.representative C.tangentRepresentative
    C.representativeOrbit C.model_continuous C.model_periodic C.modelPeriod_pos
    C.widthDirection_unit C.distanceError_nonneg C.model_width C.initial_close
    C.initial_perimeter_lower C.width_gap

end PathMetric

theorem paper_main_theorem_of_gaugeControlledFamilyNonnegative
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    {c dlt P0 P1 khat G1 Cg : ℝ}
    (G : PathMetric.GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (C : PathMetric.GaugeControlledClosingInputsNonnegative Q R M c dlt) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ), IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) = range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L :=
  paper_main_theorem_of_configured_controlledJunctions model
    (PathMetric.PaperControlledJunctionInputs.ofGaugeControlledFamilyNonnegative
      model G hmetric C)

/-- Paper conclusion directly from a configured model, completed gauge family,
and the remaining explicit range/closing data. -/
theorem paper_main_theorem_of_gaugeControlledFamily
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (G : PathMetric.GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (C : PathMetric.GaugeControlledClosingInputs Q R M c kmin dlt) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L :=
  paper_main_theorem_of_configured_controlledJunctions model
    (PathMetric.PaperControlledJunctionInputs.ofGaugeControlledFamily
      model G hmetric C)
