import Mathlib
import UnitTangentIterates.HairpinPulseIdentity
import UnitTangentIterates.HairpinArclength
import UnitTangentIterates.FrontPeriodizationIntegral
import UnitTangentIterates.TranslatorTranslation

/-!
# The front curvature of the translating hairpin

The theorem *Curvature-measure matching* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* compares the closed rear curvature `k_H` with the
periodized front curvature `K_P`, both written against the **same** isolated
profile `K_*`.  Two relations enter:

```
  y(s) = √(1 - y²)·K_*(x(s)),        (rear)
  K_*(s) = y(s) + G(y(s))·y'(s),     (front)
```

the first of which is proved for the hairpin in `HairpinPulseIdentity.lean`.
This file proves the second, which is the point at which the *fixed-point*
character of the translator enters: the front of the pair is the unit-tangent
image of the hairpin, and it is a translate of the hairpin itself only because
the profile solves `f = sin θ · cot(g θ − θ)`.

Write `g` for the tangent-angle map of the translator (`g θ = θ + δ(θ)` with
`δ = arctan K_*`), so that the two relations the fixed point provides are

* `g θ − θ = arctan(G(θ))`, i.e. the shift is the steering angle, and
* `f(g θ)·g'(θ) = f(θ) + cos θ`, the derivative of `∫_θ^{g θ} f = sin θ`

(both are proved for the constructed profile in `TranslatorTranslation.lean`).
From them:

* `curvField_next` : `G(g θ) = g'(θ)·G₂(θ)` — the curvature of the hairpin at
  the *image* angle is the derivative of the tangent-angle map times the
  steering pulse;
* `pulse_add_G_mul_deriv` : **the front relation**
  `y + G(y)y' = G(g(w))`, `w = θ ∘ x` the pulse state;
* `phase_eq` : the rear arclength of the image angle is `s + s₀`, with the
  constant phase `s₀ = S(g(π/2))`;
* `front_curvature_identity` : `K_*(s + s₀) = y(s) + G(y(s))y'(s)`;
* `front_curvature_identity_shifted` : with the pulse phased by the front
  origin, `ỹ(s) = y(s − s₀)`, this is exactly
  `K_*(s) = ỹ(s) + G(ỹ(s))ỹ'(s)`, the relation the matching theorem consumes;
* `hairpin_front_periodization_error_curv` : consequently the front
  periodization error of the hairpin, with `K̄_P` the periodization of the
  **true** isolated curvature `K_* = G ∘ θ`.

As elsewhere in this project the profile is taken smooth and positive on the
whole line (a smooth positive extension of the profile of Section 3 across the
endpoints); only its values on `(0, π)` enter the conclusions.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

open scoped ContDiff

namespace HairpinFrontCurvature

open HairpinRelative FrontPeriodization

variable {f g gp : ℝ → ℝ}

/-! ### The steering angle of the translator -/

/-- The curvature field is positive on `(0, π)`. -/
theorem curvField_pos (hfpos : ∀ t, 0 < f t) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    0 < curvField f θ :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (hfpos θ)

/-- The shift of the tangent-angle map is a steering angle: it lies in
`(0, π/2)`. -/
theorem delta_mem (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) : g θ - θ ∈ Ioo 0 (π / 2) := by
  rw [hdelta θ hθ]
  exact ⟨Real.arctan_pos.mpr (curvField_pos hfpos hθ), Real.arctan_lt_pi_div_two _⟩

/-- The steering angle has positive cosine. -/
theorem cos_delta_pos (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) : 0 < Real.cos (g θ - θ) := by
  have h := delta_mem hfpos hdelta hθ
  refine Real.cos_pos_of_mem_Ioo ⟨?_, h.2⟩
  linarith [h.1, Real.pi_pos]

/-- The pulse field is the sine of the steering angle. -/
theorem pulseField_eq_sin_delta
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    pulseField f θ = Real.sin (g θ - θ) := by
  rw [pulseField_eq_sin_arctan, hdelta θ hθ]

/-- The own speed of the rear track is the cosine of the steering angle. -/
theorem sqrt_one_sub_pulse_sq (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    Real.sqrt (1 - pulseField f θ ^ 2) = Real.cos (g θ - θ) := by
  have hcos := cos_delta_pos hfpos hdelta hθ
  rw [pulseField_eq_sin_delta hdelta hθ]
  have hsq : 1 - Real.sin (g θ - θ) ^ 2 = Real.cos (g θ - θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (g θ - θ)
    linarith
  rw [hsq, Real.sqrt_sq hcos.le]

/-- The fixed-point relation in the form `sin θ · cos δ = f(θ)·sin δ`. -/
theorem sin_mul_cos_delta (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    Real.sin θ * Real.cos (g θ - θ) = f θ * Real.sin (g θ - θ) := by
  have hcos := cos_delta_pos hfpos hdelta hθ
  have htan : Real.tan (g θ - θ) = curvField f θ := by
    rw [hdelta θ hθ, Real.tan_arctan]
  rw [Real.tan_eq_sin_div_cos, curvField, div_eq_div_iff hcos.ne' (hfpos θ).ne'] at htan
  linarith

/-- **The curvature at the image angle.**  For the translator, the curvature of
the hairpin at the image `g θ` of the tangent angle is the derivative of the
tangent-angle map times the steering pulse at `θ`.  This is the only place
where the fixed-point character of the profile is used. -/
theorem curvField_next (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    curvField f (g θ) = gp θ * pulseField f θ := by
  have hrel := sin_mul_cos_delta hfpos hdelta hθ
  set d : ℝ := g θ - θ with hd
  have hgd : g θ = θ + d := by rw [hd]; ring
  have hsin : Real.sin (g θ) = (f θ + Real.cos θ) * Real.sin d := by
    rw [hgd, Real.sin_add]
    nlinarith [hrel]
  have hfg : f (g θ) ≠ 0 := (hfpos _).ne'
  rw [curvField, hsin, ← hnextd θ hθ, pulseField_eq_sin_delta hdelta hθ, ← hd]
  field_simp

/-! ### The front relation along the pulse state -/

variable {theta x : ℝ → ℝ}

/-- The pulse state is continuous. -/
theorem continuous_state
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) :
    Continuous fun s => theta (x s) :=
  continuous_iff_continuousAt.2 fun s => (hxderiv s).continuousAt

/-- **The derivative of the steering pulse.**  Along the front arclength the
pulse `y = sin δ(w)` has derivative `cos δ(w)·(g'(w) − 1)·y`. -/
theorem hasDerivAt_pulse
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    (s : ℝ) :
    HasDerivAt (fun s => pulseField f (theta (x s)))
      (Real.cos (g (theta (x s)) - theta (x s))
        * ((gp (theta (x s)) - 1) * pulseField f (theta (x s)))) s := by
  have hw : Continuous fun s => theta (x s) := continuous_state hxderiv
  have hd1 : HasDerivAt (fun σ => g (theta (x σ)) - theta (x σ))
      (gp (theta (x s)) * pulseField f (theta (x s)) - pulseField f (theta (x s))) s :=
    ((hg (theta (x s)) (hmem (x s))).comp s (hxderiv s)).sub (hxderiv s)
  have hd2 : HasDerivAt (fun σ => Real.sin (g (theta (x σ)) - theta (x σ)))
      (Real.cos (g (theta (x s)) - theta (x s))
        * (gp (theta (x s)) * pulseField f (theta (x s)) - pulseField f (theta (x s)))) s :=
    (Real.hasDerivAt_sin _).comp s hd1
  have hev : (fun σ => pulseField f (theta (x σ)))
      =ᶠ[𝓝 s] fun σ => Real.sin (g (theta (x σ)) - theta (x σ)) := by
    filter_upwards [hw.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hmem (x s)))]
      with σ hσ using pulseField_eq_sin_delta hdelta hσ
  have := hd2.congr_of_eventuallyEq hev
  convert this using 1
  ring

/-- **The front relation.**  The isolated front curvature `y + G(y)y'`, read in
the front arclength, is the curvature of the hairpin at the image angle
`g(w)`. -/
theorem pulse_add_G_mul_deriv (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    {yp : ℝ → ℝ}
    (hy : ∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) (s : ℝ) :
    pulseField f (theta (x s)) + G (pulseField f (theta (x s))) * yp s
      = curvField f (g (theta (x s))) := by
  have hcos := cos_delta_pos hfpos hdelta (hmem (x s))
  have hval : yp s = Real.cos (g (theta (x s)) - theta (x s))
      * ((gp (theta (x s)) - 1) * pulseField f (theta (x s))) :=
    (hy s).unique (hasDerivAt_pulse hdelta hg hmem hxderiv s)
  have hG : G (pulseField f (theta (x s)))
      = (Real.cos (g (theta (x s)) - theta (x s)))⁻¹ := by
    rw [G, sqrt_one_sub_pulse_sq hfpos hdelta (hmem (x s))]
  rw [hval, hG, curvField_next hfpos hdelta hnextd (hmem (x s))]
  field_simp
  ring

/-! ### The common phase -/

/-- The image angle, read in the arclength of the hairpin, advances at unit
speed: the front is traversed at unit speed by the front arclength. -/
theorem hasDerivAt_phase (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    (s : ℝ) :
    HasDerivAt (fun σ => Hairpin.hairpinArclength f (π / 2) (g (theta (x σ)))) 1 s := by
  have hgm := hgmem _ (hmem (x s))
  have hA : HasDerivAt (Hairpin.hairpinArclength f (π / 2))
      (f (g (theta (x s))) / Real.sin (g (theta (x s)))) (g (theta (x s))) :=
    HairpinArclength.hasDerivAt_arclength hf.continuous.continuousOn hgm
  have hd1 : HasDerivAt (fun σ => g (theta (x σ)))
      (gp (theta (x s)) * pulseField f (theta (x s))) s :=
    (hg (theta (x s)) (hmem (x s))).comp s (hxderiv s)
  have hcomp := hA.comp s hd1
  have hkey : curvField f (g (theta (x s))) = gp (theta (x s)) * pulseField f (theta (x s)) :=
    curvField_next hfpos hdelta hnextd (hmem (x s))
  have hpos : 0 < curvField f (g (theta (x s))) := curvField_pos hfpos hgm
  have heq : f (g (theta (x s))) / Real.sin (g (theta (x s)))
      * (gp (theta (x s)) * pulseField f (theta (x s))) = 1 := by
    rw [← hkey, curvField]
    have hs : Real.sin (g (theta (x s))) ≠ 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi hgm.1 hgm.2
      exact this.ne'
    field_simp
    exact div_self (hfpos _).ne'
  rw [heq] at hcomp
  exact hcomp

/-- A positive lower bound for the profile on `[0, π]`. -/
theorem exists_profile_lower_bound (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t := by
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hf.continuous.continuousOn
  exact ⟨f t₀, hfpos t₀, fun t ht => hmin ⟨ht.1.le, ht.2.le⟩⟩

/-- The tangent angle at arclength `0` is `π/2`. -/
theorem theta_zero (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hvalθ : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) :
    theta 0 = π / 2 := by
  obtain ⟨m, hm, hlow⟩ := exists_profile_lower_bound hf hfpos
  have hmono := HairpinArclength.strictMonoOn_arclength hf.continuous.continuousOn hm hlow
  have hhalf : (π / 2) ∈ Ioo (0:ℝ) π :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  refine hmono.injOn (hmem 0) hhalf ?_
  rw [hvalθ 0, Hairpin.hairpinArclength]
  simp

/-- **The common phase.**  The arclength of the image angle is the front
arclength shifted by the constant `s₀ = S(g(π/2))`. -/
theorem phase_eq (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hvalθ : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    (s : ℝ) :
    Hairpin.hairpinArclength f (π / 2) (g (theta (x s)))
      = s + Hairpin.hairpinArclength f (π / 2) (g (π / 2)) := by
  set psi : ℝ → ℝ := fun σ => Hairpin.hairpinArclength f (π / 2) (g (theta (x σ))) with hpsi
  have hd : ∀ σ, HasDerivAt psi 1 σ := fun σ =>
    hasDerivAt_phase hf hfpos hdelta hgmem hnextd hg hmem hxderiv σ
  have hconst : ∀ σ, psi σ - σ = psi 0 - 0 := by
    have hz : ∀ σ, HasDerivAt (fun τ => psi τ - τ) 0 σ := by
      intro σ
      simpa using (hd σ).sub (hasDerivAt_id σ)
    intro σ
    exact is_const_of_deriv_eq_zero (fun τ => (hz τ).differentiableAt)
      (fun τ => (hz τ).deriv) σ 0
  have h0 : psi 0 = Hairpin.hairpinArclength f (π / 2) (g (π / 2)) := by
    have hx0 : x 0 = 0 :=
      HairpinPulseIdentity.pulseInverse_zero hf hfpos hderiv hxinv
    rw [hpsi]
    simp only [hx0]
    rw [theta_zero hf hfpos hmem hvalθ]
  have := hconst s
  rw [h0] at this
  linarith [this]

/-- The tangent angle at arclength `s + s₀` is the image angle. -/
theorem theta_phase_eq (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hvalθ : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    (s : ℝ) :
    theta (s + Hairpin.hairpinArclength f (π / 2) (g (π / 2))) = g (theta (x s)) := by
  obtain ⟨m, hm, hlow⟩ := exists_profile_lower_bound hf hfpos
  have hmono := HairpinArclength.strictMonoOn_arclength hf.continuous.continuousOn hm hlow
  refine hmono.injOn (hmem _) (hgmem _ (hmem (x s))) ?_
  rw [hvalθ, phase_eq hf hfpos hdelta hgmem hnextd hg hmem hvalθ hderiv hxinv hxderiv s]

/-! ### The front curvature identity -/

/-- **The front relation for the translating hairpin.**  With `K_* = G ∘ θ` the
curvature of the hairpin in its own arclength, `y` the steering pulse in the
front arclength and `s₀ = S(g(π/2))` the phase between the two origins,

`K_*(s + s₀) = y(s) + G(y(s))·y'(s)`.

This is the relation `K_* = y + G(y)y'` of the lemma *Front periodization
error*, with the phase convention made explicit. -/
theorem front_curvature_identity (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hvalθ : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    {yp : ℝ → ℝ}
    (hy : ∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) (s : ℝ) :
    curvField f (theta (s + Hairpin.hairpinArclength f (π / 2) (g (π / 2))))
      = pulseField f (theta (x s)) + G (pulseField f (theta (x s))) * yp s := by
  rw [theta_phase_eq hf hfpos hdelta hgmem hnextd hg hmem hvalθ hderiv hxinv hxderiv s,
    pulse_add_G_mul_deriv hfpos hdelta hnextd hg hmem hxderiv hy s]

/-- **The front relation, phased by the front origin.**  Writing the steering
pulse in the front arclength phased so that its origin corresponds to the
origin of the intrinsic arclength — `ỹ(s) = y(s − s₀)` — the isolated
curvature of the hairpin is exactly `K_* = ỹ + G(ỹ)ỹ'`.  This is the relation
consumed by the theorem *Curvature-measure matching*. -/
theorem front_curvature_identity_shifted (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hvalθ : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hxderiv : ∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    {yp : ℝ → ℝ}
    (hy : ∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) (s : ℝ) :
    curvField f (theta s)
      = pulseField f (theta (x (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2)))))
        + G (pulseField f (theta (x (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2))))))
          * yp (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2))) := by
  have h := front_curvature_identity hf hfpos hdelta hgmem hnextd hg hmem hvalθ hderiv
    hxinv hxderiv hy (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2)))
  rwa [sub_add_cancel] at h

/-! ### The relations are those of the profile of Section 3

The two relations used above — that the shift of the tangent-angle map is the
steering angle, and that `f(g θ)g'(θ) = f(θ) + cos θ` — are exactly what the
profile constructed in Section 3 satisfies on `(0, π)`.  (That profile is
continuous, and smooth, on the open interval only, so it is not itself an
admissible `f` for the statements above, which are phrased with the smooth
positive extension used throughout this project.) -/

/-- **The translator relations hold for the constructed profile.**  The
profile of the theorem *Translating hairpin* has a tangent-angle map
`g θ = θ + arctan(sin θ / f θ)` mapping `(0, π)` into itself, differentiable,
and satisfying `f(g θ)·g'(θ) = f(θ) + cos θ`. -/
theorem exists_translator_relations {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f g gp : ℝ → ℝ, (∀ t, 0 < f t) ∧ ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ)) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ) := by
  obtain ⟨f, hmeas, hfl, hfu, hcont, hmapsShift, hintEq, harctan, -⟩ :=
    BarrierEstimates.exists_hairpin_profile hε hε'
  have hm1 : 1 < ε⁻¹ - ε := BarrierEstimates.m_gt_one hε hε'
  have hm0 : (0:ℝ) < ε⁻¹ - ε := lt_trans zero_lt_one hm1
  have hlow : ∀ t, ε⁻¹ - ε ≤ f t := fun t =>
    le_trans ((Barriers.fMinus_min hε).1 t) (hfl t)
  have hup : ∀ t, f t ≤ ε⁻¹ + 4 / 3 + 3 * ε := fun t =>
    le_trans (hfu t) ((BarrierEstimates.profile_fPlus hε).upper t)
  have hfpos : ∀ t, 0 < f t := fun t => lt_of_lt_of_le hm0 (hlow t)
  have hprof : TranslatorOperator.Profile (ε⁻¹ - ε) (ε⁻¹ + 4 / 3 + 3 * ε) f :=
    ⟨hmeas, hlow, hup⟩
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := hprof.int
  set g : ℝ → ℝ := fun θ => θ + TranslatorOperator.shift f θ with hgdef
  have hmaps : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π := by
    intro θ hθ
    have h := hmapsShift θ hθ
    exact ⟨lt_trans hθ.1 h.1, h.2⟩
  have hAsub : ∀ x y : ℝ, Hairpin.hairpinZ f y - Hairpin.hairpinZ f x = ∫ t in x..y, f t := by
    intro x y
    simpa [Hairpin.hairpinZ] using
      intervalIntegral.integral_interval_sub_left (hint (π / 2) y) (hint (π / 2) x)
  have hU : ∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..g θ, f t) = Real.sin θ := hintEq
  have hg : ∀ θ ∈ Ioo (0:ℝ) π,
      HasDerivAt g ((f θ + Real.cos θ) / f (g θ)) θ := fun θ hθ =>
    TranslatorShift.hasDerivAt_shift hint hAsub hmeas hm0 hlow hcont hU hmaps hθ
  refine ⟨f, g, fun θ => (f θ + Real.cos θ) / f (g θ), hfpos, hcont, ?_, hmaps, ?_, hg⟩
  · intro θ hθ
    have h : g θ - θ = TranslatorOperator.shift f θ := by rw [hgdef]; ring
    rw [h, harctan θ hθ, curvField]
  · intro θ hθ
    have hne : f (g θ) ≠ 0 := (hfpos _).ne'
    field_simp

/-! ### The front periodization error with the true isolated curvature

`FrontPeriodizationHairpin.hairpin_front_periodization_error` bounds the
distance between the periodized front `K_P = Y_P + G(Y_P)Y_P'` and the sum of
the translates of the *formal* isolated profile `y + G(y)y'`.  With the front
relation above that profile is the actual curvature `K_* = G ∘ θ` of the
hairpin, once the pulse is phased by the front origin, so the error term is now
one between the two objects the matching theorem compares. -/

open PerimeterHairpinPulse FrontPeriodizationIntegral in
/-- **The front periodization error of the hairpin, against its own
curvature.**  For a profile satisfying the translator relations, the periodized
front `K_P = Y_P + G(Y_P)Y_P'` built from the steering pulse phased by the
front origin differs, in `L¹` over one period, from the periodization
`∑_m K_*(· − mP)` of the **true** isolated curvature `K_* = G ∘ θ` of the
hairpin by at most `Lip(a)·D·(8C²/(α−β))e^{2βB}·e^{−βH}`. -/
theorem hairpin_front_periodization_error_curv (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ) :
    ∃ (theta x yp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) ∧
      (∀ s, curvField f (theta s)
        = pulseField f (theta (x (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2)))))
          + G (pulseField f (theta (x (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2))))))
            * yp (s - Hairpin.hairpinArclength f (π / 2) (g (π / 2)))) ∧
      (∀ P beta H B q : ℝ, threshold alpha C b ≤ P → 0 < beta → beta < alpha →
        2 ≤ beta * P → H - 2 * B ≤ P →
        (∫ u in q..(q + P),
            |(curvField f (theta u)
                + ∑' j : {j : ℤ // j ≠ 0}, curvField f (theta (u - (j : ℤ) * P)))
              - ((∑' m : ℤ, pulseField f (theta (x (u - m * P
                    - Hairpin.hairpinArclength f (π / 2) (g (π / 2))))))
                + G (∑' m : ℤ, pulseField f (theta (x (u - m * P
                    - Hairpin.hairpinArclength f (π / 2) (g (π / 2))))))
                  * (∑' m : ℤ, yp (u - m * P
                      - Hairpin.hairpinArclength f (π / 2) (g (π / 2)))))|)
          ≤ (lipConst ((1 + b) / 2) * D * (8 * C ^ 2 / (alpha - beta))
              * Real.exp (2 * beta * B)) * Real.exp (-(beta * H))) := by
  obtain ⟨theta, x, yp, alpha, C0, D, b, halpha, hC0, hD0, hb0, hb1, -, -, -,
    hmem, hvalθ, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, hy, hypc, -, hrel⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data hf hfpos
  set s0 : ℝ := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  set C : ℝ := C0 * Real.exp (alpha * |s0|) with hCdef
  have hC : 0 ≤ C := by positivity
  set yt : ℝ → ℝ := fun s => pulseField f (theta (x (s - s0))) with hyt
  set ypt : ℝ → ℝ := fun s => yp (s - s0) with hypt
  have hshift : Continuous fun s : ℝ => s - s0 := continuous_id.sub continuous_const
  have hytc : Continuous yt := hycont.comp hshift
  have hyptc : Continuous ypt := hypc.comp hshift
  have hyt0 : ∀ s, 0 ≤ yt s := fun s => hy0 _
  have hytsup : ∀ s, yt s ≤ b := fun s => hsup _
  have hytb : ∀ s, yt s ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    refine (hyb (s - s0)).trans ?_
    rw [hCdef, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
    have h : |s| - |s0| ≤ |s - s0| := abs_sub_abs_le_abs_sub s s0
    nlinarith [halpha]
  have hytrel : ∀ s, |ypt s| ≤ D * yt s := fun s => hrel _
  have hident : ∀ s, curvField f (theta s) = yt s + G (yt s) * ypt s := fun s =>
    front_curvature_identity_shifted hf hfpos hdelta hgmem hnextd hg hmem hvalθ hderiv
      hxinv hxderiv hy s
  refine ⟨theta, x, yp, alpha, C, D, b, halpha, hC, hD0, hb0, hb1, hmem, hvalθ, hderiv,
    hxinv, hxderiv, hy, hident, ?_⟩
  intro P beta H B q hP hbeta0 hba hbP hPH
  have hPpos : 0 < P := lt_of_lt_of_le (threshold_pos halpha hC hb1) hP
  have hhalf : Real.exp (-(beta * P)) ≤ 1 / 2 := by
    have h := exp_neg_le_inv (t := beta * P) (by positivity)
    have hinv : (1:ℝ) / (beta * P) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hbP
    linarith
  have hYa : ∀ u : ℝ, (∑' m : ℤ, yt (u - m * P)) ≤ (1 + b) / 2 :=
    periodization_le_mid halpha hb1 hyt0 hytb hytsup hP
  exact FrontPeriodizationIntegral.front_periodization_error_exp
    (y := yt) (yp := ypt) (C := C) (alpha := alpha) (beta := beta)
    (a := (1 + b) / 2) (D := D) (P := P)
    (Kstar := fun u => curvField f (theta u))
    (Kbar := fun u => curvField f (theta u)
      + ∑' j : {j : ℤ // j ≠ 0}, curvField f (theta (u - (j : ℤ) * P)))
    (KP := fun u => (∑' m : ℤ, yt (u - m * P))
      + G (∑' m : ℤ, yt (u - m * P)) * (∑' m : ℤ, ypt (u - m * P)))
    (H := H) (B := B) (q := q)
    halpha hPpos hbeta0 hba hhalf hytc hyptc hyt0 hytb hD0 hytrel
    (by linarith) (by linarith) hYa hident (fun _ => rfl) (fun _ => rfl) hPH

end HairpinFrontCurvature
