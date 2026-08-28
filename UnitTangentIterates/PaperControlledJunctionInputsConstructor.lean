import Mathlib
import UnitTangentIterates.ControlledJunctionVariableSpeedDistance
import UnitTangentIterates.PaperControlledJunctionInputs
import UnitTangentIterates.UnconditionalAssemblyRemainder

/-! # Smart constructor for paper controlled-junction inputs -/

open Filter Function Set Topology

namespace PathMetric

open NormalPath

/-- Assemble the paper input bundle from variable-speed controlled junctions.

The generic theory supplies marked distance control, closed-tube passage,
ovality, and the initial positive-period certificate.  Consequently the
explicit arguments are only the concrete interpolation/gauge exports: the
junction sequences and costs, their variable-speed bounds and tube membership,
the transported representative orbit, and the terminal model comparison. -/
noncomputable def PaperControlledJunctionInputs.ofVariableSpeed
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (_model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    (S : ∀ n, ControlledJunctionSequence (Q n))
    (e : ℕ → ℕ → ℝ)
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (he0 : ∀ n k, 0 ≤ e n k)
    (hesum : ∀ n, Summable (e n))
    (hcost : ∀ n k, NormalPath.cost ((S n).path k) ≤ e n k)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (hvariable : ∀ n k,
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg ((S n).path k))
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n,
        range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
          range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    {LM d Cw H : ℝ} {u : ℂ}
    (hM : Continuous M) (hMper : Periodic M LM) (hLM : 0 < LM)
    (hu : ‖u‖ = 1) (hd0 : 0 ≤ d)
    (hMw : Width.width (range M) u ≤ Cw)
    (hclose : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M) ≤ d)
    (hperimeter : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * H - d ≤ MarkedSpace.perim (X 0))
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    PaperControlledJunctionInputs Q R M := by
  refine
    { sequence := S
      error := e
      c := c
      kmin := kmin
      dlt := dlt
      metricConstant :=
        NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg
      error_nonneg := he0
      error_summable := hesum
      path_cost := hcost
      metricConstant_nonneg := hconst
      step_distance := fun n =>
        controlledJunction_distances_variableSpeed (S n) (htube n) (hvariable n)
      tube := htube
      tube_closed := ?_
      representative := hrepresentative
      tangent_representative := htangentRepresentative
      representative_orbit := hRorbit
      limit_oval := ?_
      modelPeriod := LM
      distanceError := d
      widthCeiling := Cw
      halfWidthFloor := H
      widthDirection := u
      model_continuous := hM
      model_periodic := hMper
      modelPeriod_pos := hLM
      widthDirection_unit := hu
      distanceError_nonneg := hd0
      model_width := hMw
      initial_regular := ?_
      initial_close := hclose
      initial_perimeter_lower := hperimeter
      width_gap := hgap }
  · intro n X hX
    exact (MarkedSpace.isClosed_tube c kmin dlt).mem_of_tendsto hX
      (Eventually.of_forall (htube n))
  · intro X hX n
    have hmem : MarkedSpace.IsTubeMember c kmin dlt (X n) :=
      (MarkedSpace.isClosed_tube c kmin dlt).mem_of_tendsto (hX n)
        (Eventually.of_forall (htube n))
    exact MarkedSpace.isOval_ev hc hkmin hdlt hmem
  · intro X hX
    have hmem : MarkedSpace.IsTubeMember c kmin dlt (X 0) :=
      (MarkedSpace.isClosed_tube c kmin dlt).mem_of_tendsto (hX 0)
        (Eventually.of_forall (htube 0))
    refine ⟨(MarkedSpace.isOval_ev hc hkmin hdlt hmem).continuous,
      MarkedSpace.perim_pos hc hmem, ?_⟩
    exact MarkedSpace.periodic_ev hc hmem

end PathMetric
