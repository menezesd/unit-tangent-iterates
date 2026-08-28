import Mathlib
import UnitTangentIterates.ControlledJunctionRangeClosing

/-!
# Abstract inputs for the paper's controlled-junction closing scheme

The concrete interpolation and variable-speed gauge constructions can target
this single interface.  It records exactly the C2-controlled junction chains,
their summable quantitative bounds, tube compactness, representative range
transport, and the terminal width-comparison certificates used by the closing
argument.  No choice of an opaque global inverse operator is built into it.
-/

open Filter Function Set Topology MainTheoremConditional

namespace PathMetric

open NormalPath

/-- Constructor-facing input bundle for the paper-faithful pullback and closing
argument.  The `ControlledJunctionSequence` fields contain the interpolation and
gauge C2 exports and their endpoint junction identifications. -/
structure PaperControlledJunctionInputs
    (Q : ℕ → ℕ → MarkedSpace.Data) (R : ℕ → ℝ → ℂ) (M : ℝ → ℂ) where
  sequence : ∀ n, ControlledJunctionSequence (Q n)
  error : ℕ → ℕ → ℝ
  c : ℝ
  kmin : ℝ
  dlt : ℝ
  metricConstant : ℝ
  error_nonneg : ∀ n k, 0 ≤ error n k
  error_summable : ∀ n, Summable (error n)
  path_cost : ∀ n k,
    NormalPath.cost ((sequence n).path k) ≤ error n k
  metricConstant_nonneg : 0 ≤ metricConstant
  step_distance : ∀ n k,
    dist (Q n k) (Q n (k + 1)) ≤
      metricConstant * NormalPath.cost ((sequence n).path k)
  tube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k)
  tube_closed : ∀ n X,
    Tendsto (Q n) atTop (𝓝 X) → MarkedSpace.IsTubeMember c kmin dlt X
  representative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, range (MarkedSpace.ev (X n)) = range (R n)
  tangent_representative : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n,
      range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
        range (UnitTangent.unitTangentMap (R n))
  representative_orbit : ∀ n,
    range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n))
  limit_oval : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, IsOval (MarkedSpace.ev (X n))
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
  initial_regular : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    Continuous (MarkedSpace.ev (X 0)) ∧
    0 < MarkedSpace.perim (X 0) ∧
    Periodic (MarkedSpace.ev (X 0)) (MarkedSpace.perim (X 0))
  /-- The paper's `d_H(X₀, Q₀) ≤ C r₀`: the limiting initial curve is Hausdorff
  close to the model.  Stated on images, as in Theorem `thm:shadow`, because the
  marked metric compares curves in a common periodic parameter while
  `MarkedSpace.ev` reparametrizes each by its own arclength. -/
  initial_close : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M) ≤ distanceError
  initial_perimeter_lower : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    2 * halfWidthFloor - distanceError ≤ MarkedSpace.perim (X 0)
  width_gap :
    widthCeiling + 2 * distanceError <
      (2 * halfWidthFloor - distanceError) / Real.pi

/-- Top-level projection of the abstract interpolation/gauge recursion package.
The conclusion has the paper's order: after the model and all quantitative
constructor data are fixed, there exist the full forward range orbit and its
initial period, with the circular closing alternative excluded. -/
theorem PaperControlledJunctionInputs.exists_noncircular_rangeOrbit
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    (I : PaperControlledJunctionInputs Q R M) :
    ∃ (Y : ℕ → ℝ → ℂ) (L : ℝ),
      (∀ n, IsOval (Y n)) ∧
      (∀ n,
        range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < L ∧ Periodic (Y 0) L ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Y 0)) L := by
  exact exists_noncircular_rangeOrbit_of_controlledJunction_limits
    I.sequence I.error_nonneg I.error_summable I.path_cost
    I.metricConstant_nonneg I.step_distance I.tube I.tube_closed R
    I.representative I.tangent_representative I.representative_orbit
    I.limit_oval I.model_continuous I.model_periodic I.modelPeriod_pos
    I.widthDirection_unit I.distanceError_nonneg I.model_width
    I.initial_regular I.initial_close I.initial_perimeter_lower I.width_gap

end PathMetric
