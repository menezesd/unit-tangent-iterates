import Mathlib
import UnitTangentIterates.RearOwnTangential

/-!
# A sup bound for the tangential drift of the selected rears

`RearOwnTangential.lean` bounds the two *arclength derivatives* of the
tangential component

`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩`

of the motion of the family `Y` of selected rear tracks written in its own
arclength.  The assembly of the path metric also asks for a bound on `ξ` itself
(the hypothesis `hRbd` of `GaugeMarkedDataOfTangential.lean`), and that bound is
not a consequence of the two derivative bounds alone: differentiating the
closing relation `Y(t, x + Q(t)) = Y(t, x)` of a family of closed curves gives

`ξ(t, x + Q(t)) = ξ(t, x) − Q'(t)`,

so `ξ` drifts by `−Q'(t)` over each period, and is bounded in `x` exactly when
the arclength period of the rears does not move.  When it does not, `ξ` is
periodic; and since it vanishes at the marked point — the base drift of the
gauge is zero whenever the marked point of the front is at rest — the mean value
inequality turns the bound on `∂_xξ` into a bound on `ξ` itself:

`|ξ(t,x)| ≤ Q(t) · sup_x |∂_xξ(t,x)| ≤ Q(t) · E₀ · κ̂/√(1−κ̂²)`,

and, the rear normal velocity being controlled by the front's through the
maximum principle for the inverse Jacobi ODE,

`|ξ(t,x)| ≤ Q(t) · E_F · κ̂/(1−κ̂²)`.

All the bounds of this file are stated at one time `t` of the path, so that the
sup bound of the front normal velocity may be the cost density `m t` itself.

Main results:

* `abs_le_of_periodic_of_deriv_le` — a periodic function vanishing at the origin
  is bounded by the period times a bound for its derivative;
* `abs_frameNormal_le_time` — the maximum principle for the inverse Jacobi ODE,
  at one time;
* `abs_partialX_frameTangential_le_time` — the bound on `∂_xξ` at one time;
* `abs_frameTangential_le_of_periodic` — the sup bound for `ξ` from a sup bound
  `E₀` for the rear normal velocity;
* `abs_frameTangential_le_of_front` — the same with `E₀` produced from the sup
  bound `E_F` of the front normal velocity at that time;
* `abs_frameTangential_le_cost` — its cost form: with the front normal velocity
  dominated by the cost density `m t` and the rear period at most `Qmax`, the
  tangential drift obeys `|ξ(t,x)| ≤ (Qmax·κ̂/(1−κ̂²))·m t`, which is exactly the
  shape `Rb t ≤ rr·m t` the assembly of the path metric asks for.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnTangentialSup

open UniformFrameBounds RearOwnTangential RearOwnFrameData

/-! ### The mean value bound for a periodic function -/

/-- **A periodic function vanishing at the origin is bounded by the period times
a bound for its derivative.** -/
theorem abs_le_of_periodic_of_deriv_le {f f' : ℝ → ℝ} {Q B : ℝ} (hQ : 0 < Q)
    (hper : Function.Periodic f Q) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hzero : f 0 = 0) (hB : ∀ x, |f' x| ≤ B) (x : ℝ) : |f x| ≤ Q * B := by
  obtain ⟨z, hz, hzx⟩ := hper.exists_mem_Ico₀ hQ x
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hmvt : ‖f z - f 0‖ ≤ B * ‖z - 0‖ := by
    refine (convex_Icc (0 : ℝ) Q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (fun y _ => (hf y).hasDerivWithinAt)
      (fun y _ => by simpa [Real.norm_eq_abs] using hB y) ⟨le_rfl, hQ.le⟩
      ⟨hz.1, hz.2.le⟩
  rw [hzero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  rw [hzx]
  have hzabs : |z| ≤ Q := by
    rw [abs_of_nonneg hz.1]
    exact hz.2.le
  calc |f z| ≤ B * |z| := hmvt
    _ ≤ B * Q := mul_le_mul_of_nonneg_left hzabs hBnn
    _ = Q * B := by ring

/-! ### The two bounds at one time of the path -/

section Rear

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ}

/-- **The maximum principle for the inverse Jacobi ODE, at one time.**  The
normal velocity of the selected rears at the time `t` is bounded by the sup
bound of the front normal velocity at that time, divided by `√(1−κ̂²)`. -/
theorem abs_frameNormal_le_time {etaF : ℝ → ℝ → ℝ} {EF kh Q t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hQ : 0 < Q)
    (hstrip0 : ∀ s, 0 ≤ δ t s) (hstrip1 : ∀ s, δ t s ≤ Real.arcsin kh)
    (hper : Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) Q)
    (hjac : ∀ x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ s, |etaF t s| ≤ EF) (x : ℝ) :
    |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ EF / Real.sqrt (1 - kh ^ 2) :=
  abs_le_of_periodic_ode hQ hper hjac
    (fun y => abs_div_cos_le_strip hkh0 hkh1 (hstrip0 (sf t y)) (hstrip1 (sf t y))
      (hEF (sf t y))) x

/-- **The bound on the arclength derivative of the tangential drift, at one
time.** -/
theorem abs_partialX_frameTangential_le_time {E0 kh t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ s, 0 ≤ δ t s) (hstrip1 : ∀ s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hE0 : ∀ x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0) (x : ℝ) :
    |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ E0 * (kh / Real.sqrt (1 - kh ^ 2)) := by
  rw [partialX_frameTangential_rearOwn hF hΘ hsteer hsf hcos hYt hYdotC hangC t x, abs_mul]
  exact mul_le_mul (hE0 x)
    (abs_tan_le_strip hkh0 hkh1 (hstrip0 (sf t x)) (hstrip1 (sf t x)))
    (abs_nonneg _) (le_trans (abs_nonneg _) (hE0 x))

/-! ### The sup bound for the tangential drift -/

/-- **The tangential drift of the selected rears is bounded by the period times
the first gauge constant.**  If the tangential component is periodic in the rear
arclength — that is, if the arclength period of the rears does not move — and
vanishes at the marked point, then a sup bound `E₀` for the normal velocity of
the rears bounds it by `Q·E₀·κ̂/√(1−κ̂²)`. -/
theorem abs_frameTangential_le_of_periodic {E0 kh Q t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hQ : 0 < Q)
    (hstrip0 : ∀ s, 0 ≤ δ t s) (hstrip1 : ∀ s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hE0 : ∀ x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0)
    (hper : Function.Periodic (frameTangential Ydot (rearOwnAngle Θ δ sf) t) Q)
    (hzero : frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0) (x : ℝ) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Q * (E0 * (kh / Real.sqrt (1 - kh ^ 2))) := by
  have hxiC : ContDiff ℝ (1 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnTangential.contDiff_frameTangential hYdotC hangC
  exact abs_le_of_periodic_of_deriv_le (f' := partialX
      (frameTangential Ydot (rearOwnAngle Θ δ sf)) t) hQ hper
    (fun y => hasDerivAt_partialX hxiC t y) hzero
    (fun y => abs_partialX_frameTangential_le_time hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer
      hsf hcos hYt hYdotC hangC hE0 y) x

/-- **The tangential drift of the selected rears, from the front alone.**  The
normal velocity of the rears is controlled by that of the fronts through the
maximum principle for the inverse Jacobi ODE, so the sup bound of the tangential
drift is `Q·E_F·κ̂/(1−κ̂²)`. -/
theorem abs_frameTangential_le_of_front {etaF : ℝ → ℝ → ℝ} {EF kh Q t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hQ : 0 < Q)
    (hstrip0 : ∀ s, 0 ≤ δ t s) (hstrip1 : ∀ s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hnper : Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) Q)
    (hjac : ∀ x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ s, |etaF t s| ≤ EF)
    (hper : Function.Periodic (frameTangential Ydot (rearOwnAngle Θ δ sf) t) Q)
    (hzero : frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0) (x : ℝ) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Q * (EF * (kh / (1 - kh ^ 2))) := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hsq
  have hE0 : ∀ x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ EF / Real.sqrt (1 - kh ^ 2) := fun y =>
    abs_frameNormal_le_time hkh0 hkh1 hQ hstrip0 hstrip1 hnper hjac hEF y
  have h := abs_frameTangential_le_of_periodic (E0 := EF / Real.sqrt (1 - kh ^ 2))
    hkh0 hkh1 hQ hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt hYdotC hangC hE0 hper hzero x
  have hval : EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2))
      = EF * (kh / (1 - kh ^ 2)) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hsq.le]
    ring
  rwa [hval] at h

/-- **The cost form of the sup bound.**  If the normal velocity of the fronts is
dominated by the cost density `m t` of the path and the arclength period of the
rears is at most `Qmax`, then the tangential drift of the selected rears obeys
`|ξ(t,x)| ≤ (Qmax·κ̂/(1−κ̂²))·m t` — the shape `Rb t ≤ rr·m t` the assembly of the
path metric asks for, with the explicit constant `rr = Qmax·κ̂/(1−κ̂²)`. -/
theorem abs_frameTangential_le_cost {etaF : ℝ → ℝ → ℝ} {kh Qmax : ℝ} {m Q : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hQpos : ∀ t, 0 < Q t) (hQmax : ∀ t, Q t ≤ Qmax)
    (hnper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ m t) (hm0 : ∀ t, 0 ≤ m t)
    (hper : ∀ t, Function.Periodic (frameTangential Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hzero : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0) (t x : ℝ) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ (Qmax * (kh / (1 - kh ^ 2))) * m t := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hkhq : 0 ≤ kh / (1 - kh ^ 2) := by positivity
  have h := abs_frameTangential_le_of_front (etaF := etaF) (EF := m t) (Q := Q t)
    hkh0 hkh1 (hQpos t) (hstrip0 t) (hstrip1 t) hF hΘ hsteer hsf hcos hYt hYdotC hangC
    (hnper t) (hjac t) (hEF t) (hper t) (hzero t) x
  refine le_trans h ?_
  have hstep : Q t * (m t * (kh / (1 - kh ^ 2)))
      ≤ Qmax * (m t * (kh / (1 - kh ^ 2))) :=
    mul_le_mul_of_nonneg_right (hQmax t) (mul_nonneg (hm0 t) hkhq)
  calc Q t * (m t * (kh / (1 - kh ^ 2)))
      ≤ Qmax * (m t * (kh / (1 - kh ^ 2))) := hstep
    _ = Qmax * (kh / (1 - kh ^ 2)) * m t := by ring

end Rear

end RearOwnTangentialSup
