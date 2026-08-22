import Mathlib
import UnitTangentIterates.RearOwnDriftFundamental
import UnitTangentIterates.RearBaseDrift
import UnitTangentIterates.SelectedInverseEmbedded

/-!
# The drift bound of the selected rears without the resting marked point

`RearOwnDriftFundamental.lean` bounds the tangential drift

`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩`

of the family of selected rear tracks on one period, but only for a path whose
*marked point is at rest*: the bound is a mean value bound started at
`ξ(t,0) = 0`, and `RearBaseDrift.lean` produces that vanishing from
`∀ t, Γ.eta t 0 = 0`.

`PinchedPathRigidity.lean` shows that this hypothesis is exactly what makes the
admissible class of the `C²` estimate empty: together with the constant speed of
the slices it forces the path to stand still.  This file removes it from the
drift bound.

The point is that the base value of the drift never has to vanish — it only has
to be *small*.  For a front moving normally, `RearBaseDrift` computes
`ξ(t,0) = −η_F(t,0)·sin δ(t,0)`, and on the selected strip `0 ≤ δ ≤ arcsin κ̂`,
so

`|ξ(t,0)| ≤ κ̂ · |η_F(t,0)| ≤ κ̂ · m t`

along any normal path, with no condition whatever on the motion of the marked
point.  Feeding that into the mean value bound in place of the vanishing gives
the drift bound on one period with the constant enlarged by `κ̂`:

`|ξ(t,x)| ≤ (κ̂ + Qmax·κ̂/(1−κ̂²))·m t`.

Main results:

* `abs_le_of_deriv_le_on_Icc_of_base` — the mean value bound on `[0,Q]` started
  from a bound at the origin instead of a zero;
* `frontBaseDrift_of_normal_base`, `abs_frontBaseDrift_le` — the base drift of a
  front moving normally, and its bound `κ̂·|η_F(t,0)|` on the selected strip;
* `abs_frameTangential_base_le` — the same bound for `ξ(t,0)`;
* `abs_frameTangential_le_of_front_on_period_of_base` — the drift bound on one
  period from a bound at the base point;
* `abs_frameTangential_le_cost_on_period_free` — its cost form, with **no**
  hypothesis on the marked point of the path.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength RearOwnMotion

namespace RearBaseDriftBound

open RearOwnDriftFundamental RearBaseDrift RearOwnTangentialSup UniformFrameBounds
  RearOwnTangential RearOwnFrameData

/-! ### The mean value bound from a bound at the origin -/

/-- **The mean value bound on `[0,Q]` started from a bound at the origin.**  This
is `RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc` with the vanishing of the
function at the origin relaxed to a bound. -/
theorem abs_le_of_deriv_le_on_Icc_of_base {f f' : ℝ → ℝ} {Q A B : ℝ} (hQ : 0 ≤ Q)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbase : |f 0| ≤ A) (hB : ∀ x, |f' x| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Q) : |f x| ≤ A + Q * B := by
  have hg : ∀ y, HasDerivAt (fun z => f z - f 0) (f' y) y := fun y => (hf y).sub_const _
  have h := abs_le_of_deriv_le_on_Icc (f := fun z => f z - f 0) (f' := f') hQ hg
    (by simp) hB hx
  have hsplit : |f x| ≤ |f x - f 0| + |f 0| := by
    simpa using abs_add_le (f x - f 0) (f 0)
  linarith

/-- **The mean value bound on a symmetric window started from a bound at the
origin.**  A function bounded by `A` at the origin whose derivative is bounded
by `B` everywhere is bounded by `A + B|x|`. -/
theorem abs_le_of_deriv_le_on_window {f f' : ℝ → ℝ} {A B : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbase : |f 0| ≤ A) (hB : ∀ x, |f' x| ≤ B)
    (x : ℝ) : |f x| ≤ A + B * |x| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := B) (fun y _ => (hf y).hasDerivWithinAt)
    (fun y _ => by simpa [Real.norm_eq_abs] using hB y) (mem_univ (0 : ℝ)) (mem_univ x)
  have h2 : |f x - f 0| ≤ B * |x| := by simpa [Real.norm_eq_abs] using h
  have hsplit : |f x| ≤ |f x - f 0| + |f 0| := by simpa using abs_add_le (f x - f 0) (f 0)
  linarith

/-! ### The base drift of a front moving normally -/

/-- **The base drift of a front moving normally**, from the velocity at the
marked point alone: if `Ḟ(t,0) = η_F(t,0)·i e^{iΘ(t,0)}` then the tangential
drift the gauge flow sees at the base point is `−η_F(t,0)·sin δ(t,0)`. -/
theorem frontBaseDrift_of_normal_base {Fdot : ℝ → ℝ → ℂ} {Θ δ eta : ℝ → ℝ → ℝ} {t : ℝ}
    (hFdot : Fdot t 0
      = (eta t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ)))) :
    frontBaseDrift Fdot Θ δ t = -(eta t 0 * Real.sin (δ t 0)) := by
  have hmul : Complex.exp (Complex.I * ((Θ t 0 : ℝ) : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * ((Θ t 0 - δ t 0 : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((δ t 0 : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hre : (Complex.I * Complex.exp (Complex.I * ((δ t 0 : ℝ) : ℂ))).re
      = -Real.sin (δ t 0) := by
    rw [mul_comm Complex.I ((δ t 0 : ℝ) : ℂ), Complex.exp_mul_I]
    simp [Complex.add_re, Complex.mul_re, Complex.sin_ofReal_re]
  calc frontBaseDrift Fdot Θ δ t
      = ((eta t 0 : ℂ) * (Complex.I
          * (Complex.exp (Complex.I * ((Θ t 0 : ℝ) : ℂ))
            * (starRingEnd ℂ) (Complex.exp (Complex.I * ((Θ t 0 - δ t 0 : ℝ) : ℂ)))))).re := by
        simp only [frontBaseDrift, hFdot]
        ring_nf
    _ = ((eta t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * ((δ t 0 : ℝ) : ℂ)))).re := by
        rw [hmul]
    _ = -(eta t 0 * Real.sin (δ t 0)) := by
        simp [hre]

/-- On the selected strip the sine of the steering angle is between `0` and
`κ̂`. -/
theorem abs_sin_steering_le {δ : ℝ → ℝ → ℝ} {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh) (t s : ℝ) :
    |Real.sin (δ t s)| ≤ kh := by
  have hmem : ∀ s', δ t s' ∈ Icc (0 : ℝ) (Real.arcsin kh) :=
    fun s' => ⟨hstrip0 t s', hstrip1 t s'⟩
  have hle : Real.sin (δ t s) ≤ kh :=
    SelectedInverseEmbedded.sin_steering_le hkh0 hkh1.le hmem s
  have hge : 0 ≤ Real.sin (δ t s) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (hstrip0 t s)
      (le_trans (hstrip1 t s)
        (le_trans (Real.arcsin_le_pi_div_two kh) (by linarith [Real.pi_pos])))
  rw [abs_of_nonneg hge]
  exact hle

/-- **The base drift of a normally moving front is bounded by `κ̂` times the
normal speed at the marked point.** -/
theorem abs_frontBaseDrift_le {Fdot : ℝ → ℝ → ℂ} {Θ δ eta : ℝ → ℝ → ℝ} {kh t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hFdot : Fdot t 0
      = (eta t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ)))) :
    |frontBaseDrift Fdot Θ δ t| ≤ kh * |eta t 0| := by
  rw [frontBaseDrift_of_normal_base hFdot, abs_neg, abs_mul]
  calc |eta t 0| * |Real.sin (δ t 0)|
      ≤ |eta t 0| * kh :=
        mul_le_mul_of_nonneg_left (abs_sin_steering_le hkh0 hkh1 hstrip0 hstrip1 t 0)
          (abs_nonneg _)
    _ = kh * |eta t 0| := by ring

/-! ### The drift bound on one period -/

section Bound

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The tangential drift of the selected rears on one period, from a bound at
the base point.**  This is
`RearOwnDriftFundamental.abs_frameTangential_le_of_front_on_period` with the
vanishing of the drift at the marked point relaxed to a bound `A`. -/
theorem abs_frameTangential_le_of_front_on_period_of_base {etaF : ℝ → ℝ → ℝ}
    {EF A kh t : ℝ}
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
    (hbase : |frameTangential Ydot (rearOwnAngle Θ δ sf) t 0| ≤ A)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t))) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ A + rearArclength (δ t) (P t) * (EF * (kh / (1 - kh ^ 2))) := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
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
  have hbound := abs_le_of_deriv_le_on_Icc_of_base
    (f := frameTangential Ydot (rearOwnAngle Θ δ sf) t)
    (f' := partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t)
    (A := A) (B := EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
    hQpos.le (fun y => hasDerivAt_partialX hxiC t y) hbase
    (fun y => abs_partialX_frameTangential_le_time hkh0 hkh1 (hstrip0 t) (hstrip1 t)
      hF hΘ hsteer hsf hcos hYt hYdotC hangC hE0 y) hx
  have hval : EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2))
      = EF * (kh / (1 - kh ^ 2)) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hsq.le]
    ring
  rwa [hval] at hbound

/-- **The tangential drift of the selected rears at the marked point, along any
normal path.**  With the velocity of the family of rears split as in
`RearBaseDrift.frameTangential_rearOwn_base` and the front moving normally at its
marked point, `|ξ(t,0)| ≤ κ̂·|η_F(t,0)|`; nothing is assumed about the motion of
the marked point. -/
theorem abs_frameTangential_base_le {Fdot : ℝ → ℝ → ℂ} {Θdot w sft eta : ℝ → ℝ → ℝ}
    {kh t : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hFdot : Fdot t 0
      = (eta t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ)))) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t 0| ≤ kh * |eta t 0| := by
  rw [frameTangential_rearOwn_base (kh := kh) hkh0 hkh1 hδc hstrip0 hstrip1 hsfinv hsft
    hYdot t]
  exact abs_frontBaseDrift_le hkh0 hkh1 hstrip0 hstrip1 hFdot

/-- **The cost form of the drift bound on one period, with no hypothesis on the
marked point.**  Along any path of fronts moving normally, with normal velocity
dominated by the cost density `m t` and rear arclength period at most `Qmax`, the
tangential drift of the selected rears obeys

`|ξ(t,x)| ≤ (κ̂ + Qmax·κ̂/(1−κ̂²))·m t`

for every `x` of one period.  This is
`RearOwnDriftFundamental.abs_frameTangential_le_cost_on_period` with the resting
marked point — the hypothesis that `PinchedPathRigidity.lean` shows to make the
admissible class of the `C²` estimate empty — removed, at the price of the extra
`κ̂` in the constant. -/
theorem abs_frameTangential_le_cost_on_period_free {etaF : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℝ → ℂ} {Θdot w sft : ℝ → ℝ → ℝ} {kh Qmax : ℝ} {m : ℝ → ℝ}
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
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hYdotsplit : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hFdot : ∀ t, Fdot t 0
      = (etaF t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ))))
    (t : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t))) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ (kh + Qmax * (kh / (1 - kh ^ 2))) * m t := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hkhq : 0 ≤ kh / (1 - kh ^ 2) := by positivity
  have hδc : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hbase : |frameTangential Ydot (rearOwnAngle Θ δ sf) t 0| ≤ kh * m t := by
    refine le_trans (abs_frameTangential_base_le (eta := etaF) hkh0 hkh1 hδc hstrip0
      hstrip1 hsfinv hsft hYdotsplit (hFdot t)) ?_
    exact mul_le_mul_of_nonneg_left (hEF t 0) hkh0
  have h := abs_frameTangential_le_of_front_on_period_of_base (etaF := etaF) (EF := m t)
    (A := kh * m t) hkh0 hkh1 (hQpos t) hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv
    hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hYdotC hangC (hjac t) (hEF t) hbase hx
  have hmono : rearArclength (δ t) (P t) * (m t * (kh / (1 - kh ^ 2)))
      ≤ Qmax * (m t * (kh / (1 - kh ^ 2))) :=
    mul_le_mul_of_nonneg_right (hQmax t) (mul_nonneg (hm0 t) hkhq)
  calc |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ kh * m t + rearArclength (δ t) (P t) * (m t * (kh / (1 - kh ^ 2))) := h
    _ ≤ kh * m t + Qmax * (m t * (kh / (1 - kh ^ 2))) := by linarith
    _ = (kh + Qmax * (kh / (1 - kh ^ 2))) * m t := by ring

/-- **The tangential drift of the selected rears on a symmetric window, from a
bound at the base point.**  The two-sided companion of
`abs_frameTangential_le_of_front_on_period_of_base`: the mean value bound is
valid at every arclength, not only on one period, because the bound on the
arclength derivative of the drift is. -/
theorem abs_frameTangential_le_of_front_on_window_of_base {etaF : ℝ → ℝ → ℝ}
    {EF A kh t : ℝ}
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
    (hbase : |frameTangential Ydot (rearOwnAngle Θ δ sf) t 0| ≤ A)
    (x : ℝ) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ A + EF * (kh / (1 - kh ^ 2)) * |x| := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
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
  have hbound := abs_le_of_deriv_le_on_window
    (f := frameTangential Ydot (rearOwnAngle Θ δ sf) t)
    (f' := partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t)
    (A := A) (B := EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
    (fun y => hasDerivAt_partialX hxiC t y) hbase
    (fun y => abs_partialX_frameTangential_le_time hkh0 hkh1 (hstrip0 t) (hstrip1 t)
      hF hΘ hsteer hsf hcos hYt hYdotC hangC hE0 y) x
  have hval : EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2))
      = EF * (kh / (1 - kh ^ 2)) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hsq.le]
    ring
  rwa [hval] at hbound

/-- **The cost form of the drift bound on a symmetric window, with no hypothesis
on the marked point.**  Along any path of fronts moving normally, with normal
velocity dominated by the cost density `m t`, the tangential drift of the
selected rears obeys `|ξ(t,x)| ≤ (κ̂ + W·κ̂/(1−κ̂²))·m t` on the window
`|x| ≤ W`.  This is the bound the gauge flow needs when its base point is
allowed to drift out of `[0, Q t]`. -/
theorem abs_frameTangential_le_cost_on_window_free {etaF : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℝ → ℂ} {Θdot w sft : ℝ → ℝ → ℝ} {kh W : ℝ} {m : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQpos : ∀ t, 0 < rearArclength (δ t) (P t))
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
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hYdotsplit : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hFdot : ∀ t, Fdot t 0
      = (etaF t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ))))
    (t : ℝ) {x : ℝ} (hx : |x| ≤ W) :
    |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ (kh + W * (kh / (1 - kh ^ 2))) * m t := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hkhq : 0 ≤ kh / (1 - kh ^ 2) := by positivity
  have hδc : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hbase : |frameTangential Ydot (rearOwnAngle Θ δ sf) t 0| ≤ kh * m t := by
    refine le_trans (abs_frameTangential_base_le (eta := etaF) hkh0 hkh1 hδc hstrip0
      hstrip1 hsfinv hsft hYdotsplit (hFdot t)) ?_
    exact mul_le_mul_of_nonneg_left (hEF t 0) hkh0
  have h := abs_frameTangential_le_of_front_on_window_of_base (etaF := etaF) (EF := m t)
    (A := kh * m t) hkh0 hkh1 (hQpos t) hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv
    hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hYdotC hangC (hjac t) (hEF t) hbase x
  have hmono : m t * (kh / (1 - kh ^ 2)) * |x| ≤ m t * (kh / (1 - kh ^ 2)) * W :=
    mul_le_mul_of_nonneg_left hx (mul_nonneg (hm0 t) hkhq)
  calc |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ kh * m t + m t * (kh / (1 - kh ^ 2)) * |x| := h
    _ ≤ kh * m t + m t * (kh / (1 - kh ^ 2)) * W := by linarith
    _ = (kh + W * (kh / (1 - kh ^ 2))) * m t := by ring

end Bound

end RearBaseDriftBound
