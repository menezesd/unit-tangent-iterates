import Mathlib
import UnitTangentIterates.RearOwnPathDistIntrinsic
import UnitTangentIterates.MixedPartials

/-!
# A moving front period forces the curvature to be constant in the arclength

The variable-period theory of the selected steering angle
(`SteeringVariablePeriod.lean`) lets the arclength period `P(t)` of the front
move along the path, but it asks the parameter derivative `K̇` of the curvature
to be periodic with that same period `P(t)`.

That combination is rigid.  If the front data close up with the period `P(t)`
(the curvature and the selected steering angle are `P(t)`-periodic), if the
selected steering angle solves `δ_s = K − sin δ` and is jointly `C²`, and if the
parameter derivative of the curvature is `P(t)`-periodic as well, then

`P'(t) · ∂_s K(t, s) = 0`   for every `t` and `s`.

So along any part of the path where the front period really moves, the front
curvature must be constant in the arclength: the front is a circle there.  This
is the steering counterpart of `GaugePeriodRigidity.lean`, which showed that a
frame bundle bounding the tangential component globally forces the rear period
to be constant, and it says precisely which extra generality a genuinely moving
period would need — the parameter derivative of the front data drifts by
`−P'(t) ∂_s(·)` over each period rather than being periodic.

The mechanism: differentiating the closing relation `δ(t, s + P t) = δ(t, s)`
in the time shows that the variation `w = ∂_tδ` drifts by `−P'(t) δ_s(t,s)` over
one period, while the mixed-partials identity `∂_s w = K̇ − cos δ · w` makes both
`w(t, · + P t)` and `w(t, ·)` solve the same linear equation; the difference of
the two computations of the derivative of the drift is exactly `−P'(t) ∂_sK`.
-/

noncomputable section

open Set Function

namespace SteeringPeriodRigidity

open RearOwnHigherRegularity RearOwnPathDistIntrinsic

variable {δ K Kd Ks : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The variation solves the linearized steering equation.**  For a jointly
`C²` family of steering angles solving `δ_s = K − sin δ`, the parameter
derivative `w = ∂_tδ` satisfies `∂_s w = K̇ − cos δ · w`. -/
theorem hasDerivAt_variation_space (hδC2 : ContDiff ℝ ((1 + 1 : ℕ)) (uncurry δ))
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hKt : ∀ t s, HasDerivAt (fun r => K r s) (Kd t s) t) (t s : ℝ) :
    HasDerivAt (partialTime δ t)
      (Kd t s - Real.cos (δ t s) * partialTime δ t s) s := by
  have hδdiff : Differentiable ℝ (uncurry δ) := hδC2.differentiable (by norm_num)
  have hwC1 : ContDiff ℝ (1 : ℕ) (uncurry (partialTime δ)) :=
    contDiff_partialTime_self hδC2
  have hwdiff : Differentiable ℝ (uncurry (partialTime δ)) := hwC1.differentiable (by norm_num)
  -- the two mixed partials agree
  have hC2 : ContDiff ℝ 2 (uncurry δ) := by
    have : ((1 + 1 : ℕ) : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by norm_num
    rwa [this] at hδC2
  have hcomm := MixedPartials.deriv_partial_comm (f := δ) hC2 t s
  -- the left-hand side is the parameter derivative of `K − sin δ`
  have hleft : deriv (fun a' => deriv (δ a') s) t
      = Kd t s - Real.cos (δ t s) * partialTime δ t s := by
    have hfun : (fun a' => deriv (δ a') s) = fun a' => K a' s - Real.sin (δ a' s) := by
      funext a'
      exact (hsteer a' s).deriv
    rw [hfun]
    have hδt : HasDerivAt (fun a' => δ a' s) (partialTime δ t s) t :=
      hasDerivAt_partialTime hδdiff t s
    exact ((hKt t s).sub (hδt.sin)).deriv
  -- the right-hand side is the arclength derivative of the variation
  have hright : (fun x' => deriv (fun a' => δ a' x') t) = partialTime δ t := by
    funext x'
    exact (hasDerivAt_partialTime hδdiff t x').deriv
  rw [hleft, hright] at hcomm
  have hdiff : DifferentiableAt ℝ (partialTime δ t) s := by
    have := (hwdiff (t, s)).comp s ((differentiableAt_const t).prodMk differentiableAt_id)
    simpa [Function.comp_def, uncurry] using this
  have := hdiff.hasDerivAt
  rwa [← hcomm] at this

/-- **The variation drifts by `−P'(t) δ_s` over one period.**  Differentiating
the closing relation `δ(t, s + P t) = δ(t, s)` in the time. -/
theorem variation_shift (hδdiff : Differentiable ℝ (uncurry δ))
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hPdiff : Differentiable ℝ P) (t s : ℝ) :
    partialTime δ t (s + P t)
      = partialTime δ t s - deriv P t * (K t s - Real.sin (δ t s)) := by
  have harc : ∀ y, partialArc δ t y = K t y - Real.sin (δ t y) := fun y =>
    (hasDerivAt_partialArc hδdiff t y).unique (hsteer t y)
  have h1 : HasDerivAt (fun r => δ r (s + P r))
      (partialTime δ t (s + P t) + deriv P t • partialArc δ t (s + P t)) t :=
    hasDerivAt_moving_point hδdiff (((hPdiff t).hasDerivAt).const_add s)
  have h2 : HasDerivAt (fun r => δ r (s + P r)) (partialTime δ t s) t := by
    have hfun : (fun r => δ r (s + P r)) = fun r => δ r s := by
      funext r; exact hdper r s
    rw [hfun]
    exact hasDerivAt_partialTime hδdiff t s
  have hkey := h2.unique h1
  rw [harc (s + P t), hdper t s, hKper t s, smul_eq_mul] at hkey
  linarith [hkey]

/-- **A moving front period forces the curvature to be constant in the
arclength.**

If the front curvature `K`, the selected steering angle `δ` and the parameter
derivative `K̇` of the curvature are all periodic with the front period `P(t)`,
`δ` being jointly `C²` and solving the steering equation `δ_s = K − sin δ`, then
`P'(t) ∂_sK(t,s) = 0`: wherever the period really moves, the front is a
circle. -/
theorem periodDeriv_mul_curvature_deriv_eq_zero
    (hδC2 : ContDiff ℝ ((1 + 1 : ℕ)) (uncurry δ))
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hKt : ∀ t s, HasDerivAt (fun r => K r s) (Kd t s) t)
    (hKs : ∀ t s, HasDerivAt (K t) (Ks t s) s)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hPdiff : Differentiable ℝ P) (t s : ℝ) :
    deriv P t * Ks t s = 0 := by
  have hδdiff : Differentiable ℝ (uncurry δ) := hδC2.differentiable (by norm_num)
  set w : ℝ → ℝ → ℝ := partialTime δ with hw
  set c : ℝ := deriv P t with hc
  -- the drift of the variation over one period
  have hshift : ∀ x, w t (x + P t) = w t x - c * (K t x - Real.sin (δ t x)) := fun x =>
    variation_shift hδdiff hsteer hdper hKper hPdiff t x
  -- the drift, as a function of the arclength, differentiated in two ways
  set h : ℝ → ℝ := fun x => w t (x + P t) - w t x with hh
  have hA : HasDerivAt h
      (Real.cos (δ t s) * (c * (K t s - Real.sin (δ t s)))) s := by
    have h1 : HasDerivAt (fun x => w t (x + P t))
        (Kd t (s + P t) - Real.cos (δ t (s + P t)) * w t (s + P t)) s := by
      have := (hasDerivAt_variation_space hδC2 hsteer hKt t (s + P t)).comp s
        ((hasDerivAt_id s).add_const (P t))
      simpa using this
    have h2 : HasDerivAt (w t) (Kd t s - Real.cos (δ t s) * w t s) s :=
      hasDerivAt_variation_space hδC2 hsteer hKt t s
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    rw [hKdper t s, hdper t s, hshift s]
    ring
  have hB : HasDerivAt h
      (-(c * (Ks t s - Real.cos (δ t s) * (K t s - Real.sin (δ t s))))) s := by
    have hfun : h = fun x => -(c * (K t x - Real.sin (δ t x))) := by
      funext x
      rw [hh]
      simp only
      rw [hshift x]
      ring
    rw [hfun]
    have := (((hKs t s).sub ((hsteer t s).sin)).const_mul c).neg
    refine this.congr_deriv ?_
    ring
  have huniq := hA.unique hB
  nlinarith [huniq]

/-- **The contrapositive form.**  A front whose curvature is non-constant in the
arclength at some point of the slice at time `t` has a stationary period there:
under the hypotheses above, `P'(t) = 0`. -/
theorem periodDeriv_eq_zero_of_curvature_nonconstant
    (hδC2 : ContDiff ℝ ((1 + 1 : ℕ)) (uncurry δ))
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hKt : ∀ t s, HasDerivAt (fun r => K r s) (Kd t s) t)
    (hKs : ∀ t s, HasDerivAt (K t) (Ks t s) s)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hPdiff : Differentiable ℝ P) {t s : ℝ} (hKs0 : Ks t s ≠ 0) :
    deriv P t = 0 := by
  have h := periodDeriv_mul_curvature_deriv_eq_zero hδC2 hsteer hKt hKs hdper hKper hKdper
    hPdiff t s
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · exact absurd h1 hKs0

end SteeringPeriodRigidity
