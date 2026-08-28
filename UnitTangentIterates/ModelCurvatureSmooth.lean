import Mathlib
import UnitTangentIterates.ModelOrbitDefect

/-!
# Smoothness of the periodized model curvature

The model curvature used in the paper is

`K_L = Y_L + (1 - Y_L^2)⁻¹ᐟ² Y_L'`.

This file isolates the regularity argument.  Once the two periodized series
`Y_L` and `Y_L'` have the required finite differentiability and `Y_L` remains
strictly inside the steering strip `|Y_L| < 1`, the curvature has the same
finite differentiability.  Thus termwise regularity of the periodization can
be proved independently from the elementary nonlinear composition below.
-/

noncomputable section

open Real
open scoped ContDiff

namespace ModelCurvatureSmooth

open FrontPeriodization ModelOrbitDefect

/-- The nonlinear model-curvature expression preserves any finite order of
smoothness, provided the periodized steering pulse stays in `(-1,1)`. -/
theorem contDiff_modelCurvature_of_periodized {n : WithTop ℕ∞} {y yd : ℝ → ℝ}
    {L : ℝ}
    (hY : ContDiff ℝ n (periodizedPulse y L))
    (hYd : ContDiff ℝ n (periodizedPulse yd L))
    (hstrip : ∀ s, |periodizedPulse y L s| < 1) :
    ContDiff ℝ n (modelCurvature y yd L) := by
  have hpos : ∀ s, 0 < 1 - periodizedPulse y L s ^ 2 := by
    intro s
    have hs := abs_lt.mp (hstrip s)
    nlinarith [sq_abs (periodizedPulse y L s)]
  have hinner : ContDiff ℝ n (fun s => 1 - periodizedPulse y L s ^ 2) :=
    contDiff_const.sub (hY.pow 2)
  have hsqrt : ContDiff ℝ n (fun s => Real.sqrt (1 - periodizedPulse y L s ^ 2)) :=
    hinner.sqrt fun s => (hpos s).ne'
  have hG : ContDiff ℝ n
      (fun s => (Real.sqrt (1 - periodizedPulse y L s ^ 2))⁻¹) :=
    hsqrt.inv fun s => (Real.sqrt_pos.mpr (hpos s)).ne'
  simpa [modelCurvature, periodizedPulse, G] using hY.add (hG.mul hYd)

/-- The `C³` instance needed by the curvature interpolation and Jacobi
estimates in the shadowing part of the paper. -/
theorem contDiff_three_modelCurvature {y yd : ℝ → ℝ} {L : ℝ}
    (hY : ContDiff ℝ 3 (periodizedPulse y L))
    (hYd : ContDiff ℝ 3 (periodizedPulse yd L))
    (hstrip : ∀ s, |periodizedPulse y L s| < 1) :
    ContDiff ℝ 3 (modelCurvature y yd L) :=
  contDiff_modelCurvature_of_periodized hY hYd hstrip

/-- Smooth periodized pulse data produce a smooth model curvature. -/
theorem contDiff_top_modelCurvature {y yd : ℝ → ℝ} {L : ℝ}
    (hY : ContDiff ℝ ∞ (periodizedPulse y L))
    (hYd : ContDiff ℝ ∞ (periodizedPulse yd L))
    (hstrip : ∀ s, |periodizedPulse y L s| < 1) :
    ContDiff ℝ ∞ (modelCurvature y yd L) :=
  contDiff_modelCurvature_of_periodized hY hYd hstrip

end ModelCurvatureSmooth

