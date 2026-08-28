import Mathlib
import UnitTangentIterates.PaperGaugeControlledFamilyAdapter
import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.ConfiguredModelPositiveWidth
import UnitTangentIterates.ComplexHausdorffWidthBridge
import UnitTangentIterates.MainThresholds
import UnitTangentIterates.MarkedCurveHausdorff

noncomputable section

open Filter Function Set Topology

namespace PathMetric

/-- Build the closing bundle around the canonical initial two-cap model.
Configured-model regularity, periodicity, and positive model period are filled
automatically.  The remaining arguments are precisely tube membership,
constructor correspondence, and quantitative shadowing/width estimates. -/
def GaugeControlledClosingInputs.ofConfiguredModelFront
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt distanceError widthCeiling : ℝ} {widthDirection : ℂ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hdir : ‖widthDirection‖ = 1) (hd0 : 0 ≤ distanceError)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
      widthDirection ≤ widthCeiling)
    (hclose : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0)))
        (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        ≤ distanceError)
    (hperimeter : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * Hs 0 - distanceError ≤ MarkedSpace.perim (X 0))
    (hgap : widthCeiling + 2 * distanceError <
      (2 * Hs 0 - distanceError) / Real.pi) :
    GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
      c kmin dlt := by
  have hcont : Continuous
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) :=
    Differentiable.continuous fun s =>
      (TwoCapPairsAssembly.front_hasDerivAt
        (theta0 := model.thetaBase) (H := Hs 0)
        (model.curvature_continuous 0) s).differentiableAt
  have hper : Periodic
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)) (2 * Hs 0) :=
    TwoCapPairsAssembly.front_periodic (theta0 := model.thetaBase)
      (H := Hs 0) (model.curvature_continuous 0)
      (model.curvature_periodic 0) (model.total_turning 0)
  exact
    { c_pos := hc
      kmin_pos := hkmin
      dlt_pos := hdlt
      tube := htube
      representative := hrepresentative
      tangentRepresentative := htangentRepresentative
      representativeOrbit := hRorbit
      modelPeriod := 2 * Hs 0
      distanceError := distanceError
      widthCeiling := widthCeiling
      halfWidthFloor := Hs 0
      widthDirection := widthDirection
      model_continuous := hcont
      model_periodic := hper
      modelPeriod_pos := by linarith [model.separation_pos 0]
      widthDirection_unit := hdir
      distanceError_nonneg := hd0
      model_width := hwidth
      initial_close := hclose
      initial_perimeter_lower := hperimeter
      width_gap := hgap }

/-- The strongest canonical-width specialization: use the actual transverse
width of the configured initial model as the closing ceiling.  Thus the model
width field is reflexive, and only the quantitative large-separation gap is
needed.  The direction is the canonical transverse direction `I`. -/
def GaugeControlledClosingInputs.ofConfiguredModelFrontExactWidth
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt distanceError : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hd0 : 0 ≤ distanceError)
    (hclose : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0)))
        (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        ≤ distanceError)
    (hperimeter : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * Hs 0 - distanceError ≤ MarkedSpace.perim (X 0))
    (hgap : Width.width
        (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I +
          2 * distanceError < (2 * Hs 0 - distanceError) / Real.pi) :
    GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
      c kmin dlt :=
  GaugeControlledClosingInputs.ofConfiguredModelFront model hc hkmin hdlt htube
    hrepresentative htangentRepresentative hRorbit (by simp) hd0 le_rfl
    hclose hperimeter hgap

/-- Feed a uniform configured-model width bound and the large-separation gap
at that bound into the exact-width constructor.  Monotonicity then supplies
the gap for the actual model width.  `WidthUniform.exists_uniform_width_bound`
and `MainThresholds.eventually_width_gap` produce precisely these two inputs. -/
def GaugeControlledClosingInputs.ofConfiguredModelFrontUniformWidth
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt distanceError Cw : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hd0 : 0 ≤ distanceError)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I ≤ Cw)
    (hclose : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0)))
        (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        ≤ distanceError)
    (hperimeter : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * Hs 0 - distanceError ≤ MarkedSpace.perim (X 0))
    (hgap : Cw + 2 * distanceError <
      (2 * Hs 0 - distanceError) / Real.pi) :
    GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
      c kmin dlt :=
  GaugeControlledClosingInputs.ofConfiguredModelFrontExactWidth model hc hkmin hdlt htube
    hrepresentative htangentRepresentative hRorbit hd0 hclose hperimeter (by linarith)

/-- The canonical width is strictly positive under the configured centered-cell
angle condition.  This is the nondegeneracy companion to the exact-width
closing constructor above. -/
theorem configuredModelFront_exactWidth_pos
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    (hangle : ∀ s ∈ Ioo (-(Hs 0 / 2)) (Hs 0 / 2),
      TwoCapPairsAssembly.frontAngle (kappas 0) model.thetaBase s ∈
        Ioo (0 : ℝ) Real.pi) :
    0 < Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I :=
  ConfiguredModelPositiveWidth.width_pos model 0 model.thetaBase hangle

/-- The exact tail output needed from summable controlled junctions at orbit
level zero.  The standard proof sums the stage bounds retained by
`exists_limit_of_summable_controlledJunctions`; separating it here makes clear
that no geometric closing assumption is hidden in the certificate. -/
structure ControlledJunctionInitialTailBound
    (Q : ℕ → ℕ → MarkedSpace.Data) (distanceError : ℝ) : Prop where
  nonneg : 0 ≤ distanceError
  limit_dist : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    dist (X 0) (Q 0 0) ≤ distanceError

/-- **The summable tail bound gives the paper's `d_H(X₀, Q₀) ≤ C r₀`.**  The
marked metric compares two curves in one common periodic parameter, whereas
`MarkedSpace.ev` reparametrizes each by its own arclength; those parametrizations
differ when the perimeters differ.  On *images* the reparametrization is
invisible, so the marked bound transfers without any comparison of perimeters —
which is exactly why Theorem `thm:shadow` states this estimate for the Hausdorff
distance. -/
theorem ControlledJunctionInitialTailBound.initial_close
    {Q : ℕ → ℕ → MarkedSpace.Data} {distanceError c kmin dlt : ℝ}
    (tail : ControlledJunctionInitialTailBound Q distanceError)
    (hc : 0 < c) (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    {M : ℝ → ℂ} (hmodel : MarkedSpace.ev (Q 0 0) = M) :
    ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M)
        ≤ distanceError := by
  intro X hX
  have hXtube : MarkedSpace.IsTubeMember c kmin dlt (X 0) :=
    (MarkedSpace.isClosed_tube c kmin dlt).mem_of_tendsto (hX 0)
      (Filter.Eventually.of_forall (htube 0))
  subst hmodel
  exact MarkedSpace.hausdorffDist_range_ev_le_of_tube hc hXtube (htube 0 0)
    tail.nonneg (tail.limit_dist X hX)

/-- The same tail bound gives the lower perimeter estimate, using the
`1`-Lipschitz perimeter functional. -/
theorem ControlledJunctionInitialTailBound.initial_perimeter_lower
    {Q : ℕ → ℕ → MarkedSpace.Data} {distanceError H : ℝ}
    (tail : ControlledJunctionInitialTailBound Q distanceError)
    (hmodelPerim : MarkedSpace.perim (Q 0 0) = 2 * H) :
    ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * H - distanceError ≤ MarkedSpace.perim (X 0) := by
  intro X hX
  have hp := MarkedSpace.abs_perim_sub_le_dist (X 0) (Q 0 0)
  have hp' : |MarkedSpace.perim (X 0) - MarkedSpace.perim (Q 0 0)| ≤
      distanceError := hp.trans (tail.limit_dist X hX)
  have hlo := (abs_le.mp hp').1
  rw [hmodelPerim] at hlo
  linarith

/-- Fully derived configured-model closing constructor.  Initial pointwise
closeness and the initial perimeter lower bound now come solely from the
summable controlled-junction tail and identification of its zeroth datum with
the canonical model. -/
def GaugeControlledClosingInputs.ofConfiguredModelFrontUniformWidthTail
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ}
    {c kmin dlt distanceError Cw : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdlt : 0 < dlt)
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (tail : ControlledJunctionInitialTailBound Q distanceError)
    (hmodel : MarkedSpace.ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : MarkedSpace.perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I ≤ Cw)
    (hgap : Cw + 2 * distanceError <
      (2 * Hs 0 - distanceError) / Real.pi) :
    GaugeControlledClosingInputs Q R
      (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
      c kmin dlt :=
  GaugeControlledClosingInputs.ofConfiguredModelFrontUniformWidth model hc hkmin hdlt htube
    hrepresentative htangentRepresentative hRorbit tail.nonneg hwidth
    (tail.initial_close hc htube hmodel)
    (tail.initial_perimeter_lower hmodelPerim) hgap

end PathMetric
