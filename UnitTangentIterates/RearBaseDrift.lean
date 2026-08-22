import Mathlib
import UnitTangentIterates.GaugeBaseFlow
import UnitTangentIterates.RearOwnMotion

/-!
# The tangential drift of the selected rears at the marked point

The gauge flow of the family of selected rears fixes the base point as soon as
the tangential component `ξ` of the motion of that family vanishes at `x = 0`
(`GaugeBaseFlow.lean`).  This file computes that number from the front.

The family of rear tracks written in its own arclength is
`Y(t, x) = R(t, sf(t, x))`, and the change of variable fixes the marked point,
`sf(t, 0) = 0`, so it does not move: `∂_t sf(t, 0) = 0`.  The velocity of the
family at the marked point is therefore the velocity of the rear track itself,

`Ẏ(t, 0) = Ḟ(t, 0) − i(Θ̇ − δ̇)(t, 0) e^{iΨ(t,0)} ,`

whose second term is normal to the rear.  Hence

`ξ(t, 0) = ⟨Ḟ(t, 0), e^{iΨ(t,0)}⟩ = frontBaseDrift` ,

the component of the *front* velocity at the marked point along the *rear*
tangent direction `Ψ = Θ − δ`.  For a front moving normally — as the slices of a
normal path do — that number is `−η_F(t,0) sin δ(t,0)`, so it vanishes exactly
when the marked point of the front is at rest (or the steering angle vanishes
there).

Main results:

* `frontBaseDrift` — the component of the front velocity at the marked point
  along the rear tangent;
* `sf_base_zero`, `sft_base_zero` — the change of variable fixes the marked
  point, at every time;
* `frameTangential_rearOwn_base` — `ξ(t, 0) = frontBaseDrift`;
* `frontBaseDrift_of_normal_motion`, `frontBaseDrift_eq_zero_of_rest` — the
  criterion for a front moving normally.
-/

noncomputable section

open Function Set Complex RearTrack RearFamilyFrame RearOwnArclength RearOwnMotion

namespace RearBaseDrift

/-- The component of the front velocity at the marked point along the rear
tangent direction `Ψ = Θ − δ`: the tangential drift the gauge flow sees at the
base point. -/
def frontBaseDrift (Fdot : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  (Fdot t 0 * (starRingEnd ℂ) (Complex.exp (Complex.I * ((Θ t 0 - δ t 0 : ℝ) : ℂ)))).re

/-- A unit complex exponential times its conjugate is `1`. -/
theorem exp_mul_conj (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ)))
      = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

/-- **The change of variable fixes the marked point.** -/
theorem sf_base_zero {δ sf : ℝ → ℝ → ℝ} {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x) (t : ℝ) :
    sf t 0 = 0 := by
  have hmono : StrictMono (rearArclength (δ t)) :=
    strictMono_rearArclength (hδc t) hkh1 hkh0 (hstrip0 t) (hstrip1 t)
  refine hmono.injective ?_
  rw [hsfinv t 0]
  simp [rearArclength]

/-- **The marked point of the family of rear tracks does not move in the
parameter**: `∂_t sf(t, 0) = 0`. -/
theorem sft_base_zero {δ sf sft : ℝ → ℝ → ℝ} {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t) (t : ℝ) :
    sft t 0 = 0 := by
  have hconst : (fun r => sf r 0) = fun _ : ℝ => (0 : ℝ) :=
    funext fun r => sf_base_zero hkh0 hkh1 hδc hstrip0 hstrip1 hsfinv r
  have h := hsft t 0
  rw [hconst] at h
  exact h.unique (hasDerivAt_const t (0 : ℝ))

/-- **The tangential drift of the family of selected rears at the marked
point** is the component of the front velocity there along the rear tangent. -/
theorem frameTangential_rearOwn_base
    {Fdot Ydot : ℝ → ℝ → ℂ} {Θ δ sf sft Θdot w : ℝ → ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (t : ℝ) :
    frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = frontBaseDrift Fdot Θ δ t := by
  have hsf0 : sf t 0 = 0 := sf_base_zero hkh0 hkh1 hδc hstrip0 hstrip1 hsfinv t
  have hsft0 : sft t 0 = 0 := sft_base_zero hkh0 hkh1 hδc hstrip0 hstrip1 hsfinv hsft t
  have hang : rearOwnAngle Θ δ sf t 0 = Θ t 0 - δ t 0 := by
    simp [rearOwnAngle, rearAngle, hsf0]
  have hY : Ydot t 0 = Fdot t 0
      - Complex.I * ((Θdot t 0 - w t 0 : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((Θ t 0 - δ t 0 : ℝ) : ℂ)) := by
    rw [hYdot t 0, hsf0, hsft0]
    simp [trackVelocity, rearAngle]
  have hE := exp_mul_conj (Θ t 0 - δ t 0)
  simp only [frameTangential, frontBaseDrift, hang, hY, sub_mul]
  rw [mul_assoc, hE]
  simp

/-! ### The criterion for a front moving normally -/

/-- **The base drift of a normally moving front.**  If the front velocity is
`Ḟ = η_F · i e^{iΘ}`, purely normal, then the tangential drift the gauge flow
sees at the base point is `−η_F(t,0) sin δ(t,0)`. -/
theorem frontBaseDrift_of_normal_motion {Fdot : ℝ → ℝ → ℂ} {Θ δ eta : ℝ → ℝ → ℝ}
    (hFdot : ∀ t s, Fdot t s = (eta t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t s : ℂ))))
    (t : ℝ) :
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
        simp only [frontBaseDrift, hFdot t 0]
        ring_nf
    _ = ((eta t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * ((δ t 0 : ℝ) : ℂ)))).re := by
        rw [hmul]
    _ = -(eta t 0 * Real.sin (δ t 0)) := by
        simp [hre]

/-- If the front does not move at its marked point, the base drift vanishes. -/
theorem frontBaseDrift_eq_zero_of_velocity_zero {Fdot : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {t : ℝ}
    (h : Fdot t 0 = 0) : frontBaseDrift Fdot Θ δ t = 0 := by
  simp [frontBaseDrift, h]

/-- **The criterion.**  For a front moving normally whose marked point is at
rest, the tangential drift of the family of selected rears vanishes at the
marked point. -/
theorem frontBaseDrift_eq_zero_of_rest {Fdot : ℝ → ℝ → ℂ} {Θ δ eta : ℝ → ℝ → ℝ}
    (hFdot : ∀ t s, Fdot t s = (eta t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t s : ℂ))))
    (hrest : ∀ t, eta t 0 = 0) (t : ℝ) :
    frontBaseDrift Fdot Θ δ t = 0 := by
  rw [frontBaseDrift_of_normal_motion hFdot t, hrest t]
  simp

end RearBaseDrift
