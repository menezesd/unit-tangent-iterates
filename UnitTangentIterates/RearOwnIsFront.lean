import Mathlib
import UnitTangentIterates.RearOwnPathDistFrame

/-!
# The selected rears are again a family of fronts

The assembly of the path metric consumes a family of **fronts**: a family
`F(t, ·)` of unit-speed curves, of tangent angle `Θ(t, ·)`, closing up with the
period `P t` and turning by `2π` over one period.  Its output is the family of
**selected rears** written in their own arclength,
`Y(t,x) = rearOwn F Θ δ sf t x` (`RearOwnArclength.lean`).

This file records that the output has the same shape as the input: the family
of selected rears, in its own arclength, is again such a family, with the rear
period `Q t = ∫₀^{P t} cos δ(t,·)` in place of `P t` and the rear tangent angle
`Ψ(t,x) = Θ(t, sf(t,x)) − δ(t, sf(t,x))` in place of `Θ`.  Hence the
construction can be iterated: the unit-tangent transform of the rear family
retraces the front, and the rear family may itself be taken as the front of a
further selected inverse.

* `hasDerivAt_rearOwnAngle` — the arclength derivative of the rear tangent
  angle is the rear curvature `tan δ`, which is nonnegative on the selected
  strip (`rearOwn_curvature_nonneg`);
* `rearOwn_is_front` — the three front relations for the rear family: unit
  speed of tangent angle `Ψ`, closing with `Q t`, and turning by `2π` over one
  period.
-/

noncomputable section

open Function Set Complex RearTrack ArclengthInverse RearOwnArclength

namespace RearOwnIsFront

variable {F : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kh : ℝ}

/-- **The curvature of the selected rear** in its own arclength: the derivative
of the rear tangent angle `Ψ = Θ − δ` is `tan δ`. -/
theorem hasDerivAt_rearOwnAngle
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hδ : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x) (t x : ℝ) :
    HasDerivAt (rearOwnAngle Θ δ sf t) (Real.tan (δ t (sf t x))) x := by
  have hang : ∀ s, HasDerivAt (fun s => Θ t s - δ t s) (Real.sin (δ t s)) s := by
    intro s
    have h := (hΘ t s).sub (hδ t s)
    refine h.congr_deriv ?_
    ring
  have h := (hang (sf t x)).comp x (hsf t x)
  refine h.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- The selected rear is convex: its curvature is nonnegative on the selected
strip. -/
theorem rearOwn_curvature_nonneg (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hkh0 : 0 ≤ kh) (t x : ℝ) : 0 ≤ Real.tan (δ t (sf t x)) := by
  have hcos : 0 < Real.cos (δ t (sf t x)) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by nlinarith))
      (Shadowing.cos_ge_of_mem_strip (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
  have hsin : 0 ≤ Real.sin (δ t (sf t x)) := by
    have hle : δ t (sf t x) ≤ Real.pi / 2 := by
      refine le_trans (hstrip1 t (sf t x)) ?_
      exact Real.arcsin_le_pi_div_two kh
    exact Real.sin_nonneg_of_nonneg_of_le_pi (hstrip0 t (sf t x)) (by linarith [Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos]
  exact div_nonneg hsin hcos.le

/-- **The family of selected rears is again a family of fronts.**

For front data satisfying the hypotheses of the path-metric assembly — unit
speed with tangent angle `Θ`, the steering equation on the selected strip, the
closing relations of the front, and the change of variable `sf` inverting the
rear arclength — the family of rear tracks written in its own arclength is a
family of unit-speed closed curves of tangent angle `Ψ = Θ ∘ sf − δ ∘ sf`,
closing up with the rear period `Q t = ∫₀^{P t} cos δ(t, ·)` and turning by
`2π` over one period.  These are exactly the three relations `hF`, `hFper`,
`hΘper` asked of a family of fronts. -/
theorem rearOwn_is_front (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hδ : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hδc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi) :
    (∀ t x, HasDerivAt (rearOwn F Θ δ sf t)
        (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))) x) ∧
      (∀ t x, rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t)) = rearOwn F Θ δ sf t x) ∧
      (∀ t x, rearOwnAngle Θ δ sf t (x + rearArclength (δ t) (P t))
        = rearOwnAngle Θ δ sf t x + 2 * Real.pi) := by
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := by
    intro t s
    have h : 0 < Real.cos (δ t s) :=
      lt_of_lt_of_le (Real.sqrt_pos.mpr (by nlinarith))
        (Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s))
    exact h.ne'
  refine ⟨fun t x => ?_, fun t x => ?_, fun t x => ?_⟩
  · exact hasDerivAt_rearOwn_space hF hΘ hδ hsf hcos t x
  · exact rearOwn_closing hkh0 hkh1 hδc hstrip0 hstrip1 hdper hsfinv hFper hΘper t x
  · exact RearOwnPathDistFrame.rearOwnAngle_shift hkh0 hkh1 hδc hstrip0 hstrip1 hdper
      hsfinv hΘper t x

end RearOwnIsFront
