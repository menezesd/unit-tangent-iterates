import Mathlib
import UnitTangentIterates.UniformFrameBounds

/-!
# The base point of the gauge flow

The path-metric bound for the family of selected rears is stated in the *gauge
parameter*: the flow `Φ` of the tangential rate `−ξ/v`, started at time `0` from
the rescaled arclength.  The marked curve the bound reaches at the final time is
the terminal slice read in that parameter, so it is the marked selected inverse
of the terminal front **only if the gauge flow fixes the base point**,
`Φ(T, 0) = 0` (`SelectedInverseRearOwnMarked.lean`).

This file supplies the criterion.  The base point is fixed exactly when the
tangential rate vanishes there: the constant function `0` is then a solution of
the flow equation with the same initial value, and two solutions of a globally
Lipschitz field that agree once agree always (`GlobalODE.lean`).

Main results:

* `eq_zero_of_flow` — a solution of a globally Lipschitz field vanishing at the
  origin, started at the origin, stays there;
* `gaugeFlow_base_fixed` — for a bundle of frame data whose tangential
  component vanishes at the base point, the gauge flow fixes the base point.
-/

noncomputable section

open Function

namespace GaugeBaseFlow

open UniformFrameBounds

/-- **A flow line started at a zero of the field stays there.**  If the field
`f` is globally Lipschitz in the state, uniformly in the time, and vanishes at
`0` at every time, then the solution with initial value `0` is identically
`0`. -/
theorem eq_zero_of_flow {f : ℝ → ℝ → ℝ} {K : NNReal} {alpha : ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (f t)) (hzero : ∀ t, f t 0 = 0)
    (halpha : ∀ t, HasDerivAt alpha (f t (alpha t)) t) (h0 : alpha 0 = 0) (t : ℝ) :
    alpha t = 0 := by
  have hconst : ∀ r : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (f r ((fun _ : ℝ => (0 : ℝ)) r)) r := by
    intro r
    simpa [hzero r] using (hasDerivAt_const r (0 : ℝ))
  have h := GlobalODE.dist_le_of_global_solutions (K := K) (f := f) (α₁ := alpha)
    (α₂ := fun _ : ℝ => (0 : ℝ)) hlip halpha hconst 0 t
  simp only [h0, dist_self, zero_mul] at h
  have : dist (alpha t) (0 : ℝ) = 0 := le_antisymm h dist_nonneg
  simpa using this

/-- **The gauge flow fixes the base point when the tangential component
vanishes there.**  For a bundle of frame data with `ξ(t, 0) = 0` at every time,
the gauge flow line through the origin is the origin. -/
theorem gaugeFlow_base_fixed (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ}
    (hPhid : ∀ t, HasDerivAt (fun r => Phi r 0)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t 0)) t)
    (hPhi0 : Phi 0 0 = 0) (hxi0 : ∀ t, D.xi t 0 = 0) (t : ℝ) :
    Phi t 0 = 0 := by
  refine eq_zero_of_flow (K := Real.toNNReal D.rateLip)
    (fun a => GaugeRate.lipschitzWith_gaugeRate_of_bound D.rateLip_nonneg D.hxi D.hv D.hvne
      D.hrate1 a) (fun a => ?_) hPhid hPhi0 t
  simp [GaugeRate.gaugeRate, hxi0 a]

end GaugeBaseFlow
