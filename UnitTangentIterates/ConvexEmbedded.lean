import Mathlib

/-!
# A convex closed curve of turning number one is embedded

The path-distance bounds for the selected inverse carry, at both ends, the
hypothesis that the rear track is **injective on one period** — that the rear
curve is embedded.  It is a global hypothesis, and it is not an independent
one: the rear track of a front of strictly positive curvature is a closed
curve whose tangent angle increases strictly and turns by exactly `2π`, and
such a curve is simple.

This file proves that.  Let `X` be a closed curve of period `L`, regular with
positive speed `v` and tangent angle `θ`,

```
  X'(s) = v(s) e^{iθ(s)} ,   v > 0 ,   θ strictly increasing,
  θ(s + L) = θ(s) + 2π .
```

Then `X` is injective on every half-open period.  The proof is the one the
paper alludes to for convexity: fix `s₁` and project on the normal at `s₁`,

```
  p(s) = Re( X(s) e^{-iα} ) ,   α = θ(s₁) + π/2 ,
  p'(s) = v(s) cos(θ(s) - α) = v(s) sin(θ(s) - θ(s₁)) .
```

Over one circuit starting at `s₁` the angle `θ - θ(s₁)` increases strictly from
`0` to `2π`, so `p` strictly increases while that angle is below `π` and
strictly decreases afterwards, while `p(s₁ + L) = p(s₁)`.  Hence `p(s) > p(s₁)`
for every `s` strictly between `s₁` and `s₁ + L`, and in particular
`X(s) ≠ X(s₁)`.

Main results:

* `hasDerivAt_projection_of_speed` — the derivative of the projection;
* `ne_of_lt_of_lt_add_period` — the two points of one circuit are distinct;
* `injOn_Ico_of_turning_one` — the curve is injective on a period.
-/

noncomputable section

open Set

namespace ConvexEmbedded

variable {X : ℝ → ℂ} {theta v : ℝ → ℝ}

/-- **The derivative of the projection of the curve on a fixed direction.**
For `X' = v e^{iθ}` the projection `p(s) = Re(X(s)e^{-iα})` has
`p'(s) = v(s) cos(θ(s) - α)`. -/
theorem hasDerivAt_projection_of_speed {s alpha : ℝ}
    (hX : HasDerivAt X ((v s : ℂ) * Complex.exp (Complex.I * (theta s : ℂ))) s) :
    HasDerivAt (fun u => (X u * Complex.exp (-(Complex.I * (alpha : ℂ)))).re)
      (v s * Real.cos (theta s - alpha)) s := by
  have hmul := hX.mul_const (Complex.exp (-(Complex.I * (alpha : ℂ))))
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hmul
  refine h.congr_deriv ?_
  have hcomb : (v s : ℂ) * Complex.exp (Complex.I * (theta s : ℂ))
        * Complex.exp (-(Complex.I * (alpha : ℂ)))
      = (v s : ℂ) * Complex.exp (((theta s - alpha : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hcomb, Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Two distinct points of one circuit are distinct points of the plane.** -/
theorem ne_of_lt_of_lt_add_period {L s₁ s₂ : ℝ}
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp (Complex.I * (theta s : ℂ))) s)
    (hv : ∀ s, 0 < v s) (hcont : Continuous theta) (hmono : StrictMono theta)
    (hturn : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hper : Function.Periodic X L)
    (h12 : s₁ < s₂) (h2L : s₂ < s₁ + L) : X s₂ ≠ X s₁ := by
  have hpi := Real.pi_pos
  set alpha : ℝ := theta s₁ + Real.pi / 2 with halpha
  set p : ℝ → ℝ := fun u => (X u * Complex.exp (-(Complex.I * (alpha : ℂ)))).re with hpdef
  have hpd : ∀ s, HasDerivAt p (v s * Real.sin (theta s - theta s₁)) s := by
    intro s
    have h := hasDerivAt_projection_of_speed (v := v) (theta := theta) (alpha := alpha) (hX s)
    refine h.congr_deriv ?_
    have hshift : theta s - alpha = (theta s - theta s₁) - Real.pi / 2 := by
      rw [halpha]; ring
    rw [hshift, Real.cos_sub_pi_div_two]
  have hpcont : Continuous p :=
    continuous_iff_continuousAt.mpr fun s => (hpd s).continuousAt
  -- the half-way point of the circuit, where the tangent has turned by `π`
  obtain ⟨m, hm, hmval⟩ : ∃ m ∈ Ioo s₁ (s₁ + L), theta m = theta s₁ + Real.pi := by
    have hsub := intermediate_value_Ioo (le_of_lt (h12.trans h2L)) hcont.continuousOn
    have hmem : theta s₁ + Real.pi ∈ Ioo (theta s₁) (theta (s₁ + L)) := by
      rw [hturn s₁]
      constructor <;> linarith
    obtain ⟨m, hm, hmval⟩ := hsub hmem
    exact ⟨m, hm, hmval⟩
  -- the projection increases up to the half-way point and decreases afterwards
  have hinc : StrictMonoOn p (Icc s₁ m) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hpcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hpd x).deriv]
    have hlo : 0 < theta x - theta s₁ := by
      have := hmono hx.1
      linarith
    have hhi : theta x - theta s₁ < Real.pi := by
      have := hmono hx.2
      rw [hmval] at this
      linarith
    have := Real.sin_pos_of_pos_of_lt_pi hlo hhi
    have hvx := hv x
    positivity
  have hdec : StrictAntiOn p (Icc m (s₁ + L)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hpcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hpd x).deriv]
    have hlo : Real.pi < theta x - theta s₁ := by
      have := hmono hx.1
      rw [hmval] at this
      linarith
    have hhi : theta x - theta s₁ < 2 * Real.pi := by
      have := hmono hx.2
      rw [hturn s₁] at this
      linarith
    have hsin : Real.sin (theta x - theta s₁) < 0 := by
      have hpos : 0 < Real.sin (theta x - theta s₁ - Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at hpos
      linarith
    have hvx := hv x
    exact mul_neg_of_pos_of_neg hvx hsin
  have hend : p (s₁ + L) = p s₁ := by rw [hpdef]; simp [hper s₁]
  have hlt : p s₁ < p s₂ := by
    rcases le_or_gt s₂ m with hcase | hcase
    · exact hinc ⟨le_rfl, hm.1.le⟩ ⟨h12.le, hcase⟩ h12
    · have := hdec ⟨hcase.le, h2L.le⟩ ⟨hm.2.le, le_rfl⟩ h2L
      rw [hend] at this
      exact this
  intro heq
  rw [hpdef] at hlt
  simp only [heq] at hlt
  exact lt_irrefl _ hlt

/-- **A closed regular curve whose tangent angle increases strictly and turns by
`2π` over a period is embedded.** -/
theorem injOn_Ico_of_turning_one {L : ℝ}
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp (Complex.I * (theta s : ℂ))) s)
    (hv : ∀ s, 0 < v s) (hcont : Continuous theta) (hmono : StrictMono theta)
    (hturn : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hper : Function.Periodic X L) (a : ℝ) :
    InjOn X (Ico a (a + L)) := by
  intro s₁ h1 s₂ h2 heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ne_of_lt_of_lt_add_period hX hv hcont hmono hturn hper hlt
      (lt_of_lt_of_le h2.2 (by linarith [h1.1])) heq.symm
  · exact ne_of_lt_of_lt_add_period hX hv hcont hmono hturn hper hlt
      (lt_of_lt_of_le h1.2 (by linarith [h2.1])) heq

end ConvexEmbedded
