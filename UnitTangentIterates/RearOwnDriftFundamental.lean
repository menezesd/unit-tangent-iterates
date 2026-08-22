import Mathlib
import UnitTangentIterates.RearOwnTangentialSup
import UnitTangentIterates.SelInvDriftRigidity

/-!
# The drift bound on one period, without assuming periodicity

`RearOwnTangentialSup.lean` bounds the tangential drift

`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩`

of the family `Y` of selected rear tracks written in its own arclength *for
every* `x`, but only under two periodicity hypotheses: that `ξ(t,·)` is periodic
with the rear period, and that the normal velocity `η(t,·)` is.  The first of
these is a genuine restriction — `SelInvDriftRigidity.lean` shows it holds
exactly along the paths whose rear arclength period does not move.

This file removes both.

* The normal hypothesis was never a hypothesis at all: differentiating the
  closing relation `Y(t, x + Q t) = Y(t, x)` gives `η(t, x + Q t) = η(t, x)`,
  so `η(t,·)` is *always* periodic with the rear period
  (`periodic_normal_of_closed`, `periodic_frameNormal_rearOwn`).
* The tangential hypothesis is only needed to move an arbitrary `x` back into a
  fundamental domain.  On the fundamental domain `[0, Q t]` itself the mean
  value inequality applies directly (`abs_le_of_deriv_le_on_Icc`), so the sup
  bound holds there for *every* path of fronts, with no constraint on the
  motion of the rear period.

Main results:

* `periodic_normal_of_closed` — the normal component of the motion of a family
  of closed curves written in its own arclength is periodic;
* `periodic_frameNormal_rearOwn` — its form for the family of selected rears;
* `abs_le_of_deriv_le_on_Icc` — the mean value bound on `[0, Q]`;
* `abs_frameTangential_le_of_front_on_period` — the sup bound for `ξ` on one
  period, from a sup bound for the front normal velocity, with no periodicity
  assumed;
* `abs_frameTangential_le_cost_on_period` — its cost form
  `|ξ(t,x)| ≤ (Qmax·κ̂/(1−κ̂²))·m t` for `x` in one period;
* `abs_frameTangential_le_cost_of_period_const` — the *global* cost bound with
  both periodicity hypotheses replaced by the single scalar condition that the
  rear arclength period be stationary.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength RearOwnMotion

namespace RearOwnDriftFundamental

open RearOwnTangentialSup SelInvDriftRigidity UniformFrameBounds RearOwnTangential
  RearOwnFrameData

/-! ### The normal component is always periodic -/

/-- **The normal component of the motion of a family of closed curves written in
its own arclength is periodic with the period.**  Unlike the tangential
component, which drifts by `−Q'(t)` over each period, the normal component
carries no drift, so no hypothesis on the motion of the period is needed. -/
theorem periodic_normal_of_closed {Y tauY : ℝ → ℝ → ℂ} {xi eta : ℝ → ℝ → ℝ}
    {Q Q' : ℝ → ℝ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((xi t x : ℂ) * tauY t x + (eta t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Q t) = Y t x)
    (hQd : ∀ t, HasDerivAt Q (Q' t) t) (t : ℝ) : Function.Periodic (eta t) (Q t) := by
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t' x h
    have hn := htaunorm t' x
    rw [h] at hn
    simp at hn
  have htauper : ∀ t, Function.Periodic (tauY t) (Q t) := by
    intro t' x
    have hshift : HasDerivAt (fun y => Y t' (y + Q t')) (tauY t' (x + Q t')) x :=
      HasDerivAt.comp_add_const x (Q t') (hYx t' (x + Q t'))
    have hfun : (fun y => Y t' (y + Q t')) = Y t' := funext fun y => hclose t' y
    rw [hfun] at hshift
    exact hshift.unique (hYx t' x)
  intro x
  exact (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).2

section Rear

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kh : ℝ}

/-- **The normal velocity of the family of selected rears is periodic in the
rear arclength**, with no hypothesis on the motion of the rear period. -/
theorem periodic_frameNormal_rearOwn
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t) (t : ℝ) :
    Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) := by
  have hδcont : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hQC : ContDiff ℝ (1 : ℕ) (rearPeriod δ P) := contDiff_rearPeriod hδC hPC
  have hQd : ∀ r, HasDerivAt (rearPeriod δ P) (deriv (rearPeriod δ P) r) r := fun r =>
    (hQC.differentiable (by norm_num) r).hasDerivAt
  exact periodic_normal_of_closed (Y := rearOwn F Θ δ sf)
    (tauY := rearOwnTangent Θ δ sf) (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
    (contDiff_one_rearOwn hFC hΘC hδC hsfC)
    (fun t' x => hasDerivAt_rearOwn_space hF hΘ hsteer hsf hcos t' x)
    (fun t' x => hasDerivAt_rearOwn_time_frame (hYt t' x))
    (fun t' x => norm_rearOwn_tangent t' x)
    (fun t' x => rearOwn_closing hkh0 hkh1 hδcont hstrip0 hstrip1 hδper hsfinv hFper
      hΘper t' x)
    hQd t

end Rear

/-! ### The mean value bound on one period -/

/-- **A function vanishing at the origin is bounded on `[0, Q]` by `Q` times a
bound for its derivative.**  This is the periodic mean value bound
`RearOwnTangentialSup.abs_le_of_periodic_of_deriv_le` with the periodicity
hypothesis dropped and the conclusion restricted to the fundamental domain. -/
theorem abs_le_of_deriv_le_on_Icc {f f' : ℝ → ℝ} {Q B : ℝ} (hQ : 0 ≤ Q)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hzero : f 0 = 0) (hB : ∀ x, |f' x| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Q) : |f x| ≤ Q * B := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hmvt : ‖f x - f 0‖ ≤ B * ‖x - 0‖ :=
    (convex_Icc (0 : ℝ) Q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (fun y _ => (hf y).hasDerivWithinAt)
      (fun y _ => by simpa [Real.norm_eq_abs] using hB y) ⟨le_rfl, hQ⟩ hx
  rw [hzero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hxabs : |x| ≤ Q := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  calc |f x| ≤ B * |x| := hmvt
    _ ≤ B * Q := mul_le_mul_of_nonneg_left hxabs hBnn
    _ = Q * B := by ring

/-! ### The drift bound on one period -/

section Bound

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The tangential drift of the selected rears on one period, from the front
alone.**  Neither the periodicity of the drift nor that of the normal velocity
is assumed: the second is automatic, and the first is only needed off the
fundamental domain. -/
theorem abs_frameTangential_le_of_front_on_period {etaF : ℝ → ℝ → ℝ} {EF kh t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQpos : 0 < rearArclength (δ t) (P t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ s, |etaF t s| ≤ EF)
    (hzero : frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t))) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ rearArclength (δ t) (P t) * (EF * (kh / (1 - kh ^ 2))) := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hsq
  have hnper : Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) :=
    periodic_frameNormal_rearOwn hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv
      hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt t
  have hE0 : ∀ y, |frameNormal Ydot (rearOwnAngle Θ δ sf) t y|
      ≤ EF / Real.sqrt (1 - kh ^ 2) := fun y =>
    abs_frameNormal_le_time hkh0 hkh1 hQpos (hstrip0 t) (hstrip1 t) hnper hjac hEF y
  have hxiC : ContDiff ℝ (1 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnTangential.contDiff_frameTangential hYdotC hangC
  have hbound := abs_le_of_deriv_le_on_Icc
    (f := frameTangential Ydot (rearOwnAngle Θ δ sf) t)
    (f' := partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t)
    (B := EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
    hQpos.le (fun y => hasDerivAt_partialX hxiC t y) hzero
    (fun y => abs_partialX_frameTangential_le_time hkh0 hkh1 (hstrip0 t) (hstrip1 t)
      hF hΘ hsteer hsf hcos hYt hYdotC hangC hE0 y) hx
  have hval : EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2))
      = EF * (kh / (1 - kh ^ 2)) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hsq.le]
    ring
  rwa [hval] at hbound

/-- **The cost form of the drift bound on one period.**  With the normal
velocity of the fronts dominated by the cost density `m t` of the path and the
rear arclength period at most `Qmax`, the tangential drift of the selected rears
obeys `|ξ(t,x)| ≤ (Qmax·κ̂/(1−κ̂²))·m t` for every `x` of one period — the shape
`Rb t ≤ rr·m t` the assembly of the path metric asks for, now with no
periodicity hypothesis on the drift and hence no constraint on the motion of the
rear period. -/
theorem abs_frameTangential_le_cost_on_period {etaF : ℝ → ℝ → ℝ} {kh Qmax : ℝ}
    {m : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQpos : ∀ t, 0 < rearArclength (δ t) (P t))
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Qmax)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ m t) (hm0 : ∀ t, 0 ≤ m t)
    (hzero : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    (t : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t))) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ (Qmax * (kh / (1 - kh ^ 2))) * m t := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hkhq : 0 ≤ kh / (1 - kh ^ 2) := by positivity
  have h := abs_frameTangential_le_of_front_on_period (etaF := etaF) (EF := m t)
    hkh0 hkh1 (hQpos t) hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv hδper hFper hΘper
    hFC hΘC hδC hsfC hPC hYt hYdotC hangC (hjac t) (hEF t) (hzero t) hx
  refine le_trans h ?_
  calc rearArclength (δ t) (P t) * (m t * (kh / (1 - kh ^ 2)))
      ≤ Qmax * (m t * (kh / (1 - kh ^ 2))) :=
        mul_le_mul_of_nonneg_right (hQmax t) (mul_nonneg (hm0 t) hkhq)
    _ = Qmax * (kh / (1 - kh ^ 2)) * m t := by ring

/-- **The global drift bound with the two periodicity hypotheses replaced by one
scalar condition.**  Both periodicity hypotheses of
`RearOwnTangentialSup.abs_frameTangential_le_cost` follow from the rear
arclength period standing still: the normal one always holds, and the tangential
one is equivalent to it.  So the global cost bound
`|ξ(t,x)| ≤ (Qmax·κ̂/(1−κ̂²))·m t` holds along every path of fronts whose rear
period is stationary. -/
theorem abs_frameTangential_le_cost_of_period_const {etaF : ℝ → ℝ → ℝ} {kh Qmax : ℝ}
    {m : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQpos : ∀ t, 0 < rearArclength (δ t) (P t))
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Qmax)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ m t) (hm0 : ∀ t, 0 ≤ m t)
    (hQ0 : ∀ t, deriv (rearPeriod δ P) t = 0)
    (hzero : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0) (t x : ℝ) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ (Qmax * (kh / (1 - kh ^ 2))) * m t := by
  have hnper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) := fun t' =>
    periodic_frameNormal_rearOwn hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv
      hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt t'
  have hper : ∀ t, Function.Periodic (frameTangential Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) := fun t' =>
    periodic_frameTangential_of_period_const hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer
      hsf hsfinv hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hQ0 t'
  exact abs_frameTangential_le_cost (etaF := etaF) (Q := fun t => rearArclength (δ t) (P t))
    hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt hYdotC hangC hQpos hQmax hnper
    hjac hEF hm0 hper hzero t x

end Bound

end RearOwnDriftFundamental
