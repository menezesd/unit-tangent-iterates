import Mathlib
import UnitTangentIterates.GaugeFlowPeriodic

/-!
# The gauge parameter of a closed family whose slices change length

`GaugeFlowPeriodic.lean` shows that the gauge flow of a closed family is a
*normalized* parameter — each flowed slice has period one — under the standing
assumption that the arclength period `Q` of the slices is the **same** at every
time.  That assumption is not innocent: the arclength period of a moving closed
curve changes with time, and it is constant only for a family that preserves
length.

This file removes it.  Let `Q t` be the arclength period of the slice at time
`t`.  Differentiating the closing relation `X(t, x + Q t) = X(t, x)` in `t`
gives, for the tangential component `ξ` of the velocity read in the arclength of
the slice,

`ξ(t, x + Q t) = ξ(t, x) − Q'(t) · v(t, x)`,

the normal component and the speed remaining `Q t`-periodic.  Hence the
tangential rate `h = −ξ/v` of the gauge flow is *quasi-periodic*:

`h(t, x + Q t) = h(t, x) + Q'(t)`,

and the flow of such a field translates by the *current* period:

`Φ(t, u + 1) = Φ(t, u) + Q t`   (`flow_translation_var`),

whenever it starts at `Φ(0, u) = Q 0 · u`.  Consequently every function of the
arclength which is `Q t`-periodic at time `t` becomes a `1`-periodic function of
the gauge parameter (`periodic_comp_flow_var`), which is exactly what the path
metric of `PathMetric.lean` requires.

Main results:

* `flow_translation_var` — the flow of a quasi-periodic field translates by the
  current period;
* `quasiPeriodic_gaugeRate` — the tangential rate of a closed family whose
  period changes is quasi-periodic;
* `periodic_comp_flow_var` — the gauge parameter is a normalized parameter.

The constant-period statements of `GaugeFlowPeriodic.lean` are the special case
`Q' = 0` (`flow_translation_var_const`).
-/

noncomputable section

open Set Function

namespace GaugeFlowVariablePeriod

/-! ### The flow of a quasi-periodic field -/

/-- **The flow of a quasi-periodic field translates by the current period.**
If the field satisfies `h(t, x + Q t) = h(t, x) + Q'(t)` and the flow starts at
`Φ(0, u) = Q 0 · u`, then `Φ(t, u + 1) = Φ(t, u) + Q t` at every time — the
gauge parameter runs over exactly one period of the slice at time `t` as `u`
runs over a unit interval, even though that period changes. -/
theorem flow_translation_var {h : ℝ → ℝ → ℝ} {K : NNReal} {Q Q' : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hqp : ∀ t x, h t (x + Q t) = h t x + Q' t)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (u t : ℝ) :
    Phi t (u + 1) = Phi t u + Q t := by
  have h1 : ∀ r, HasDerivAt (fun r' => Phi r' (u + 1)) (h r (Phi r (u + 1))) r :=
    fun r => hPhid (u + 1) r
  have h2 : ∀ r, HasDerivAt (fun r' => Phi r' u + Q r') (h r (Phi r u + Q r)) r := by
    intro r
    have hd : HasDerivAt (fun r' => Phi r' u + Q r') (h r (Phi r u) + Q' r) r :=
      (hPhid u r).add (hQd r)
    rwa [← hqp r (Phi r u)] at hd
  have h0 : dist ((fun r' => Phi r' (u + 1)) 0) ((fun r' => Phi r' u + Q r') 0) = 0 := by
    simp only [hPhi0]
    rw [dist_eq_zero]
    ring
  have hb := GlobalODE.dist_le_of_global_solutions (K := K) hlip h1 h2 0 t
  rw [h0, zero_mul] at hb
  have := le_antisymm hb dist_nonneg
  simpa [dist_eq_zero] using this

/-- The constant-period case: with `Q' = 0` the hypothesis of
`flow_translation_var` is the periodicity of the field, and the conclusion is
`GaugeFlowPeriodic.flow_translation`. -/
theorem flow_translation_var_const {h : ℝ → ℝ → ℝ} {K : NNReal} {Q : ℝ} {Phi : ℝ → ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hper : ∀ t, Function.Periodic (h t) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u) (u t : ℝ) :
    Phi t (u + 1) = Phi t u + Q :=
  flow_translation_var (Q := fun _ => Q) (Q' := fun _ => 0) hlip
    (fun t => hasDerivAt_const t Q) (fun t x => by rw [hper t x]; ring) hPhid hPhi0 u t

/-- **The hypotheses are non-vacuous with a genuinely changing period.**  The
linear field `h(t,x) = x`, whose flow started at `Q₀u` is `Φ(t,u) = Q₀ue^t`, is
quasi-periodic for the exponentially growing period `Q t = Q₀e^t`, and the flow
translates by that current period. -/
example (Q0 u t : ℝ) :
    Q0 * (u + 1) * Real.exp t = Q0 * u * Real.exp t + Q0 * Real.exp t :=
  flow_translation_var (h := fun _ x => x) (K := 1) (Q := fun t => Q0 * Real.exp t)
    (Q' := fun t => Q0 * Real.exp t) (Phi := fun t u => Q0 * u * Real.exp t)
    (fun _ => LipschitzWith.id) (fun t => (Real.hasDerivAt_exp t).const_mul Q0)
    (fun _ _ => rfl)
    (fun u t => by
      simpa [mul_assoc] using (Real.hasDerivAt_exp t).const_mul (Q0 * u))
    (fun u => by simp) u t

/-! ### The tangential rate of a closed family whose period changes -/

/-- **The tangential rate of a closed family is quasi-periodic.**  If the speed
is `Q t`-periodic and the tangential component of the velocity satisfies the
closing relation `ξ(t, x + Q t) = ξ(t, x) − Q'(t) v(t, x)` obtained by
differentiating `X(t, x + Q t) = X(t, x)` in `t`, then the rate `−ξ/v` of the
gauge flow satisfies `h(t, x + Q t) = h(t, x) + Q'(t)`. -/
theorem quasiPeriodic_gaugeRate {xi v : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hvne : ∀ t x, v t x ≠ 0)
    (hvper : ∀ t, Function.Periodic (v t) (Q t))
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t * v t x) (t x : ℝ) :
    GaugeRate.gaugeRate xi v t (x + Q t) = GaugeRate.gaugeRate xi v t x + Q' t := by
  have hv : v t x ≠ 0 := hvne t x
  simp only [GaugeRate.gaugeRate, hxiqp t x, hvper t x]
  field_simp
  ring

/-! ### The gauge parameter is a normalized parameter -/

/-- **A function of the arclength which is `Q t`-periodic at time `t` becomes a
`1`-periodic function of the gauge parameter**, even though the period of the
slices changes. -/
theorem periodic_comp_flow_var {α : Type*} {h : ℝ → ℝ → ℝ} {K : NNReal} {Q Q' : ℝ → ℝ}
    {Phi : ℝ → ℝ → ℝ} {G : ℝ → ℝ → α}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hqp : ∀ t x, h t (x + Q t) = h t x + Q' t)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hG : ∀ t, Function.Periodic (G t) (Q t)) (t : ℝ) :
    Function.Periodic (fun u => G t (Phi t u)) 1 := by
  intro u
  simp only
  rw [flow_translation_var hlip hQd hqp hPhid hPhi0 u t, hG t (Phi t u)]

/-- **The gauge parameter of a closed family with changing period, for the frame
data of a bundle.**  The two hypotheses on the frame data are the closing
relations of a family whose arclength period `Q t` changes with time; the
conclusion is that the flowed slice has period one at every time. -/
theorem gauge_parameter_normalized_var (D : UniformFrameBounds.GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hG : ∀ t, Function.Periodic (G t) (Q t)) (t : ℝ) :
    Function.Periodic (fun u => G t (Phi t u)) 1 :=
  periodic_comp_flow_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
    (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 hG t

end GaugeFlowVariablePeriod
