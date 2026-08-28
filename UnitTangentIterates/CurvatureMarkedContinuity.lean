import UnitTangentIterates.CurvatureFromMarkedDistance
import UnitTangentIterates.TubePullbackLimit

/-!
# Curvature is continuous in the marked datum, hence converges along limits
-/

noncomputable section

open Set Function Filter Topology Complex MarkedSpace CurvatureFromMarkedDistance

namespace CurvatureFromMarkedDistance

/-- Evaluating the velocity component at a fixed parameter is continuous. -/
theorem continuous_vel_apply (u : ℝ) : Continuous (fun p : Data => p.2.1 u) :=
  (ContinuousEvalConst.continuous_eval_const u).comp
    (continuous_fst.comp continuous_snd)

/-- Evaluating the acceleration component at a fixed parameter is continuous. -/
theorem continuous_acc_apply (u : ℝ) : Continuous (fun p : Data => p.2.2 u) :=
  (ContinuousEvalConst.continuous_eval_const u).comp
    (continuous_snd.comp continuous_snd)

/-- **The curvature at a fixed parameter is continuous at every marked datum of
nonzero speed there.**  The numerator is bilinear in the velocity and the
acceleration and the denominator is a power of the speed. -/
theorem continuousAt_dataCurv {X : Data} {u : ℝ} (hX : ‖X.2.1 u‖ ≠ 0) :
    ContinuousAt (fun p : Data => dataCurv p u) X := by
  have hv : ContinuousAt (fun p : Data => p.2.1 u) X :=
    (continuous_vel_apply u).continuousAt
  have ha : ContinuousAt (fun p : Data => p.2.2 u) X :=
    (continuous_acc_apply u).continuousAt
  have hnum : ContinuousAt
      (fun p : Data => ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im) X :=
    (Complex.continuous_im.continuousAt).comp
      ((continuous_conj.continuousAt.comp hv).mul ha)
  have hden : ContinuousAt (fun p : Data => ‖p.2.1 u‖ ^ 3) X :=
    (hv.norm).pow 3
  exact hnum.div hden (by simpa using pow_ne_zero 3 hX)

/-- **Curvature converges pointwise along a convergent sequence of marked
data**, provided the limit has nonzero speed at the parameter in question.
This is the only way the approximants enter
`UnconditionalAssembly.limitStrictnessDataH_of_tendsto`. -/
theorem tendsto_dataCurv {P : ℕ → Data} {X : Data} {u : ℝ}
    (hP : Tendsto P atTop (𝓝 X)) (hX : ‖X.2.1 u‖ ≠ 0) :
    Tendsto (fun k => dataCurv (P k) u) atTop (𝓝 (dataCurv X u)) :=
  (continuousAt_dataCurv hX).tendsto.comp hP

/-- The speed of a tube member is bounded below by `c`, so a tube member with
`0 < c` has nonzero speed everywhere. -/
theorem speed_ne_zero {c kmin dlt : ℝ} {p : Data} (hc : 0 < c)
    (hp : IsTubeMember c kmin dlt p) (u : ℝ) : ‖p.2.1 u‖ ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le hc (hp.speed_lb u))

/-- **Curvature converges along the shadowing limit.** -/
theorem tendsto_dataCurv_of_tube {P : ℕ → Data} {X : Data} {c kmin dlt : ℝ}
    (hc : 0 < c) (hX : IsTubeMember c kmin dlt X)
    (hP : Tendsto P atTop (𝓝 X)) (u : ℝ) :
    Tendsto (fun k => dataCurv (P k) u) atTop (𝓝 (dataCurv X u)) :=
  tendsto_dataCurv hP (speed_ne_zero hc hX u)

end CurvatureFromMarkedDistance
