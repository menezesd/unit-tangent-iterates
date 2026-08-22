import Mathlib
import UnitTangentIterates.UniformFrameBounds
import UnitTangentIterates.GaugeClosingRelations

/-!
# The gauge frame bundle forces the period to be constant

A moving family of closed curves, each written in its own arclength, obeys the
closing relations of `GaugeClosingRelations.lean`: the normal component of the
velocity is periodic with the current period `Q t`, while the tangential
component only satisfies

`ξ(t, x + Q t) = ξ(t, x) − Q'(t) v(t, x)`.

Iterating that relation `n` times gives `ξ(t, x + nQ t) = ξ(t,x) − n Q'(t) v(t,x)`,
because the speed is periodic.  So a tangential component which is *bounded* —
as the bundle `UniformFrameBounds.GaugeFrameData` requires, through its constant
`A₀` — forces `Q'(t) v(t,x) = 0`, and hence `Q'(t) = 0` since the speed never
vanishes.

The consequence for the assembly of the path metric in the normal gauge is
recorded in `rearFamily_period_constant`: whenever a family of closed curves
written in its own arclength moves with the tangential component of a gauge
frame bundle — the hypotheses of
`GaugePathRearFamily.pathDist_le_of_rear_family` — its arclength period is the
same at every time.  The generality of the variable-period chain
(`GaugeFlowVariablePeriod.lean` and the files built on it) is therefore not
reached by those statements: they apply exactly to the paths along which the
length of the moving curve does not change.

Main results: `constant_period_of_bounded_tangential`,
`GaugeFrameData.periodDeriv_eq_zero`, `rearFamily_period_constant`.
-/

noncomputable section

open Set Function

namespace GaugePeriodRigidity

open UniformFrameBounds

/-- Iterating the quasi-periodicity relation: the tangential component drifts by
`n Q'(t) v(t,x)` over `n` periods. -/
theorem tangential_iterate {xi v : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hvper : ∀ t, Function.Periodic (v t) (Q t))
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t * v t x) (t x : ℝ) :
    ∀ n : ℕ, xi t (x + n * Q t) = xi t x - n * (Q' t * v t x) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : x + ((n : ℝ) + 1) * Q t = (x + n * Q t) + Q t := by ring
      have hvn : v t (x + n * Q t) = v t x := (hvper t).nat_mul n x
      rw [Nat.cast_succ, hstep, hxiqp t (x + n * Q t), ih, hvn]
      ring

/-- **A bounded tangential component forces the period to be constant.**  If the
speed of the family is periodic with the current period and never vanishes, and
the tangential component of the motion is globally bounded, then the derivative
of the period vanishes. -/
theorem constant_period_of_bounded_tangential {xi v : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ} {A0 : ℝ}
    (hA0 : ∀ t x, |xi t x| ≤ A0) (hvne : ∀ t x, v t x ≠ 0)
    (hvper : ∀ t, Function.Periodic (v t) (Q t))
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t * v t x) (t : ℝ) :
    Q' t = 0 := by
  have hzero : Q' t * v t 0 = 0 := by
    by_contra hne
    have hpos : 0 < |Q' t * v t 0| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * A0 / |Q' t * v t 0|)
    have hkey := tangential_iterate hvper hxiqp t 0 n
    have h1 : |xi t (0 + n * Q t)| ≤ A0 := hA0 _ _
    have h2 : |xi t 0| ≤ A0 := hA0 _ _
    have h3 : (n : ℝ) * |Q' t * v t 0| ≤ 2 * A0 := by
      have : |(n : ℝ) * (Q' t * v t 0)| ≤ |xi t 0| + |xi t (0 + n * Q t)| := by
        have hrw : (n : ℝ) * (Q' t * v t 0) = xi t 0 - xi t (0 + n * Q t) := by
          rw [hkey]; ring
        rw [hrw]
        exact abs_sub _ _
      calc (n : ℝ) * |Q' t * v t 0| = |(n : ℝ) * (Q' t * v t 0)| := by
            simp [abs_mul]
        _ ≤ |xi t 0| + |xi t (0 + n * Q t)| := this
        _ ≤ 2 * A0 := by linarith
    have hlt : 2 * A0 < (n : ℝ) * |Q' t * v t 0| := by
      rw [div_lt_iff₀ hpos] at hn
      linarith
    linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h (hvne t 0)

/-- **The period of a closed family moving with a bounded tangential component
is constant.** -/
theorem _root_.UniformFrameBounds.GaugeFrameData.periodDeriv_eq_zero (D : GaugeFrameData)
    {A0 : ℝ} (hA0 : ∀ t x, |D.xi t x| ≤ A0)
    {Q Q' : ℝ → ℝ} (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x) (t : ℝ) :
    Q' t = 0 :=
  constant_period_of_bounded_tangential hA0 D.hvne hvper hxiqp t

/-- **A family of closed curves written in its own arclength, moving with a
bounded tangential component of unit speed, has constant arclength period.**

These are the hypotheses that
`GaugePathRearFamily.pathDist_le_of_rear_family` places on the family of rear
tracks, *together with* a global bound on the tangential component; so that
statement reaches paths along which the length of the rear changes only through
bundles whose tangential component is unbounded, which is exactly what
`RearOwnFrameDrift.lean` constructs. -/
theorem rearFamily_period_constant {Y tauY : ℝ → ℝ → ℂ} {etaR : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {A0 : ℝ} (hA0 : ∀ t x, |D.xi t x| ≤ A0) {Qf Qf' : ℝ → ℝ}
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t) (t : ℝ) :
    Qf' t = 0 := by
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t x h
    have hn := htaunorm t x
    rw [h] at hn
    simp at hn
  have htauper : ∀ t, Function.Periodic (tauY t) (Qf t) := by
    intro t x
    have hshift : HasDerivAt (fun y => Y t (y + Qf t)) (tauY t (x + Qf t)) x :=
      HasDerivAt.comp_add_const x (Qf t) (hYx t (x + Qf t))
    have hfun : (fun y => Y t (y + Qf t)) = Y t := funext fun y => hclose t y
    rw [hfun] at hshift
    exact hshift.unique (hYx t x)
  have hqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x := by
    intro t x
    have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).1
    rw [h, hv1]
    ring
  exact D.periodDeriv_eq_zero hA0 (fun t x => by simp [hv1]) hqp t

end GaugePeriodRigidity
