import Mathlib
import UnitTangentIterates.GaugeFlowPeriodic

/-!
# The densities of a closed slice in the gauge parameter

The path metric of `PathMetric.lean` measures a normal path through the four
densities of the normal velocity, taken in the **normalized parameter** `u` (in
which every slice has period one):

`∫₀¹ |η|`, `‖η‖_∞`, `‖∂_u η‖_∞`, `‖∂_u²η‖_∞`.

The normal gauge of `NormalGaugeFamily.lean` supplies exactly such a parameter:
`u ↦ Φ(t, u)`, the gauge flow started at `Φ(0, u) = Qu`, where `Q` is the period
of the reference slice in arclength — `GaugeFlowPeriodic.lean` shows it has
period one at every time.

This file converts the four densities of the flowed slice `u ↦ η(Φ(t, u))` into
the corresponding densities of `η` in **arclength**, which are the quantities
the paper's inverse Jacobi estimates control.  The sup norms pick up the
distortion factors of `GaugeFunctionals.lean`, and the `L¹` density is compared
with the integral over one period of arclength — the flow translating by exactly
one period as `u` runs over one unit.

Main result: `gauge_densities_le`.
-/

noncomputable section

open Set Function MarkedTopology

namespace GaugeDensities

open UniformFrameBounds GaugeFlowPeriodic

/-- **The densities of the flowed slice, in terms of the densities in
arclength.**  For the gauge flow of a closed family, started at `Φ(0,u) = Qu`
with `Q` the period of the reference slice, the four densities of the path
metric of the flowed normal velocity `u ↦ η(Φ(t,u))` are bounded by those of
`η` in arclength, with the distortion factors of the gauge flow. -/
theorem gauge_densities_le (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hxiper : ∀ a, Function.Periodic (D.xi a) Q) (hvper : ∀ a, Function.Periodic (D.v a) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ (2 : ℕ) eta) (hper : Function.Periodic eta Q) (t : ℝ) :
    supNorm (fun u => eta (Phi t u)) ≤ supNorm eta ∧
    supNorm (iteratedDeriv 1 fun u => eta (Phi t u))
        ≤ supNorm (deriv eta) * (Q * Real.exp (D.rateLip * |t|)) ∧
    supNorm (iteratedDeriv 2 fun u => eta (Phi t u))
        ≤ supNorm (deriv (deriv eta)) * (Q * Real.exp (D.rateLip * |t|)) ^ 2
          + supNorm (deriv eta)
              * (D.rateBound2 * Q ^ 2 * |t| * Real.exp (2 * D.rateLip * |t|)) ∧
    (∫ u in (0:ℝ)..1, |eta (Phi t u)|)
        ≤ (Real.exp (D.rateLip * |t|) / Q) * ∫ x in (0:ℝ)..Q, |eta x| := by
  obtain ⟨h0, h1, h2, hL1⟩ :=
    D.gauge_functionals_comparison_periodic (Q := Q) (ell := Q) (Phi := Phi) hQ heta hper
      hQ hPhi0 hPhid (a := 0) (b := 1) zero_le_one t
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h1
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h2
  · -- the flow translates by exactly one period as `u` runs over one unit
    have htrans : Phi t 1 = Phi t 0 + Q := by
      have := flow_translation (K := Real.toNNReal D.rateLip)
        D.lipschitzWith_gaugeRate (periodic_gaugeRate hxiper hvper) hPhid hPhi0 0 t
      simpa using this
    have habs : Function.Periodic (fun x => |eta x|) Q := fun x => by
      simp [hper x]
    have hshift : (∫ x in (Phi t 0)..(Phi t 1), |eta x|) = ∫ x in (0:ℝ)..Q, |eta x| := by
      rw [htrans]
      simpa using habs.intervalIntegral_add_eq (Phi t 0) 0
    have hfac : 1 / (Q * Real.exp (-(D.rateLip * |t|))) = Real.exp (D.rateLip * |t|) / Q := by
      rw [Real.exp_neg]
      field_simp
    rw [hshift, hfac] at hL1
    exact hL1

end GaugeDensities
