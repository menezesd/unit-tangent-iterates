import Mathlib
import UnitTangentIterates.GaugeDensities
import UnitTangentIterates.GaugeFlowVariablePeriod

/-!
# The densities of a closed slice in the gauge parameter, with a changing period

`GaugeDensities.gauge_densities_le` bounds the four densities of the path metric
of the flowed normal velocity `u ↦ η(Φ(t,u))` by the densities of `η` in
arclength, for a family all of whose slices have the *same* arclength period
`Q`.

This file removes that restriction.  The period `Q t` of the slice at time `t`
is now a differentiable function of the time; the frame data obeys the closing
relations of such a family — the speed is `Q t`-periodic and the tangential
component satisfies `ξ(t, x + Q t) = ξ(t, x) − Q'(t) v(t, x)` — and the normal
velocity `η` of the slice at time `t` is `Q t`-periodic.

Nothing changes in the three sup-norm comparisons: they only involve the
distortion of the gauge flow, whose reference length is the period `Q 0` of the
initial slice.  In the `L¹` comparison the interval of arclength is the *current*
period: as `u` runs over a unit interval, the gauge parameter runs over one
period of the slice at time `t`, by
`GaugeFlowVariablePeriod.flow_translation_var`.

Main result: `gauge_densities_le_var`.
-/

noncomputable section

open Set Function MarkedTopology

namespace GaugeDensitiesVariable

open UniformFrameBounds GaugeFlowVariablePeriod

/-- **The densities of the flowed slice, in terms of the densities in
arclength, for a family whose slices change length.**  For the gauge flow of a
closed family of arclength period `Q t` at time `t`, started at
`Φ(0,u) = Q 0 · u`, the four densities of the path metric of the flowed normal
velocity `u ↦ η(Φ(t,u))` are bounded by those of `η` in arclength — the `L¹`
density by the integral over one period of the *current* slice. -/
theorem gauge_densities_le_var (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (t : ℝ)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ (2 : ℕ) eta) (hper : Function.Periodic eta (Q t)) :
    supNorm (fun u => eta (Phi t u)) ≤ supNorm eta ∧
    supNorm (iteratedDeriv 1 fun u => eta (Phi t u))
        ≤ supNorm (deriv eta) * (Q 0 * Real.exp (D.rateLip * |t|)) ∧
    supNorm (iteratedDeriv 2 fun u => eta (Phi t u))
        ≤ supNorm (deriv (deriv eta)) * (Q 0 * Real.exp (D.rateLip * |t|)) ^ 2
          + supNorm (deriv eta)
              * (D.rateBound2 * Q 0 ^ 2 * |t| * Real.exp (2 * D.rateLip * |t|)) ∧
    (∫ u in (0:ℝ)..1, |eta (Phi t u)|)
        ≤ (Real.exp (D.rateLip * |t|) / Q 0) * ∫ x in (0:ℝ)..(Q t), |eta x| := by
  obtain ⟨h0, h1, h2, hL1⟩ :=
    D.gauge_functionals_comparison_periodic (Q := Q t) (ell := Q 0) (Phi := Phi) (hQpos t)
      heta hper (hQpos 0) hPhi0 hPhid (a := 0) (b := 1) zero_le_one t
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h1
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h2
  · -- as `u` runs over a unit interval the flow translates by the current period
    have htrans : Phi t 1 = Phi t 0 + Q t := by
      have := flow_translation_var (K := Real.toNNReal D.rateLip)
        D.lipschitzWith_gaugeRate hQd (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid
        hPhi0 0 t
      simpa using this
    have habs : Function.Periodic (fun x => |eta x|) (Q t) := fun x => by
      simp [hper x]
    have hshift : (∫ x in (Phi t 0)..(Phi t 1), |eta x|) = ∫ x in (0:ℝ)..(Q t), |eta x| := by
      rw [htrans]
      simpa using habs.intervalIntegral_add_eq (Phi t 0) 0
    have hfac : 1 / (Q 0 * Real.exp (-(D.rateLip * |t|)))
        = Real.exp (D.rateLip * |t|) / Q 0 := by
      rw [Real.exp_neg]
      field_simp
    rw [hshift, hfac] at hL1
    exact hL1

end GaugeDensitiesVariable
