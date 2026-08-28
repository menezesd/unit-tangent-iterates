import Mathlib
import UnitTangentIterates.PeriodizedTurning
import UnitTangentIterates.ModelCurvatureSmooth

/-!
# Finite smoothness of exponentially decaying periodizations

`PeriodizedTurning.hasDerivAt_periodization` justifies one termwise
differentiation of an exponentially decaying translate series.  This file
iterates that result in the `ContDiff` hierarchy.  In particular, four
successive pulse functions `y₀,y₁,y₂,y₃`, with `yⱼ' = yⱼ₊₁`, give a `C³`
periodized pulse.  A fifth function gives the simultaneous `C³` regularity of
the periodizations of `y₀` and `y₁` required by the model-curvature formula.
-/

noncomputable section

open Real
open scoped ContDiff

namespace PeriodizedPulseSmooth

open ModelOrbitDefect

/-- One step of the periodization regularity bootstrap. -/
theorem contDiff_succ_periodizedPulse {n : ℕ} {y yd : ℝ → ℝ}
    {C alpha P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hy : ∀ x, HasDerivAt y (yd x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hydb : ∀ x, |yd x| ≤ C * Real.exp (-alpha * |x|))
    (hYd : ContDiff ℝ (n : ℕ) (periodizedPulse yd P)) :
    ContDiff ℝ (n + 1 : ℕ) (periodizedPulse y P) := by
  have hD : ∀ x, HasDerivAt (periodizedPulse y P) (periodizedPulse yd P x) x := by
    intro x
    simpa [periodizedPulse] using
      PeriodizedTurning.hasDerivAt_periodization halpha hP hy hyb hydb x
  have hdiff : Differentiable ℝ (periodizedPulse y P) :=
    fun x => (hD x).differentiableAt
  have hderiv : deriv (periodizedPulse y P) = periodizedPulse yd P :=
    funext fun x => (hD x).deriv
  have key : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) (periodizedPulse y P) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiff, by simp, ?_⟩
    rw [hderiv]
    exact hYd
  exact_mod_cast key

/-- A continuous exponentially decaying pulse has a `C⁰` periodization. -/
theorem contDiff_zero_periodizedPulse {y : ℝ → ℝ} {C alpha P : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P) (hy : Continuous y)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|)) :
    ContDiff ℝ (0 : ℕ) (periodizedPulse y P) := by
  simpa [contDiff_zero, periodizedPulse] using
    PeriodizedTurning.continuous_periodization halpha hP hy hyb

/-- Three termwise differentiations give a `C³` periodized pulse. -/
theorem contDiff_three_periodizedPulse {y0 y1 y2 y3 : ℝ → ℝ}
    {C alpha P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (h01 : ∀ x, HasDerivAt y0 (y1 x) x)
    (h12 : ∀ x, HasDerivAt y1 (y2 x) x)
    (h23 : ∀ x, HasDerivAt y2 (y3 x) x)
    (hy3 : Continuous y3)
    (hb0 : ∀ x, |y0 x| ≤ C * Real.exp (-alpha * |x|))
    (hb1 : ∀ x, |y1 x| ≤ C * Real.exp (-alpha * |x|))
    (hb2 : ∀ x, |y2 x| ≤ C * Real.exp (-alpha * |x|))
    (hb3 : ∀ x, |y3 x| ≤ C * Real.exp (-alpha * |x|)) :
    ContDiff ℝ (3 : ℕ) (periodizedPulse y0 P) := by
  have hY3 : ContDiff ℝ (0 : ℕ) (periodizedPulse y3 P) :=
    contDiff_zero_periodizedPulse halpha hP hy3 hb3
  have hY2 : ContDiff ℝ (1 : ℕ) (periodizedPulse y2 P) := by
    simpa using contDiff_succ_periodizedPulse halpha hP h23 hb2 hb3 hY3
  have hY1 : ContDiff ℝ (2 : ℕ) (periodizedPulse y1 P) := by
    simpa using contDiff_succ_periodizedPulse halpha hP h12 hb1 hb2 hY2
  simpa using contDiff_succ_periodizedPulse halpha hP h01 hb0 hb1 hY1

/-- Five exponentially decaying members of a derivative chain supply the two
`C³` periodizations in `ModelCurvatureSmooth.contDiff_three_modelCurvature`. -/
theorem contDiff_three_modelCurvature_of_derivative_chain
    {y0 y1 y2 y3 y4 : ℝ → ℝ} {C alpha P : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P)
    (h01 : ∀ x, HasDerivAt y0 (y1 x) x)
    (h12 : ∀ x, HasDerivAt y1 (y2 x) x)
    (h23 : ∀ x, HasDerivAt y2 (y3 x) x)
    (h34 : ∀ x, HasDerivAt y3 (y4 x) x)
    (hy3 : Continuous y3) (hy4 : Continuous y4)
    (hb0 : ∀ x, |y0 x| ≤ C * Real.exp (-alpha * |x|))
    (hb1 : ∀ x, |y1 x| ≤ C * Real.exp (-alpha * |x|))
    (hb2 : ∀ x, |y2 x| ≤ C * Real.exp (-alpha * |x|))
    (hb3 : ∀ x, |y3 x| ≤ C * Real.exp (-alpha * |x|))
    (hb4 : ∀ x, |y4 x| ≤ C * Real.exp (-alpha * |x|))
    (hstrip : ∀ s, |periodizedPulse y0 P s| < 1) :
    ContDiff ℝ (3 : ℕ) (modelCurvature y0 y1 P) := by
  have hY0 : ContDiff ℝ (3 : ℕ) (periodizedPulse y0 P) :=
    contDiff_three_periodizedPulse halpha hP h01 h12 h23 hy3 hb0 hb1 hb2 hb3
  have hY1 : ContDiff ℝ (3 : ℕ) (periodizedPulse y1 P) :=
    contDiff_three_periodizedPulse halpha hP h12 h23 h34 hy4 hb1 hb2 hb3 hb4
  exact ModelCurvatureSmooth.contDiff_three_modelCurvature hY0 hY1 hstrip

end PeriodizedPulseSmooth
