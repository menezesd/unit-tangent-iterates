import Mathlib
import UnitTangentIterates.HairpinPulseDecay
import UnitTangentIterates.HairpinMass

/-!
# The lower comparison `K_* ≥ b₀ y` for the hairpin

The last estimate of the lemma **Hairpin pulse estimates** of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* is the lower comparison

```
  K_*(s) ≥ b₀ y(s)
```

between the curvature and the steering pulse *at the same arclength value*.
Its proof, formalized in `HairpinMass.Kstar_lower_bound` in the abstract, is:
the relative bound `|K_*'| ≤ C K_*` makes the logarithmic derivative of `K_*`
bounded, hence a bounded shift changes `K_*` by at most the factor `e^{-CD}`
(the bounded-shift Harnack inequality); the shift between the front and the
rear arclength is bounded; and `K_*(x(s)) = y(s)/c(s) ≥ y(s)`.

This file supplies the two missing ingredients for the hairpin — the bound on
the logarithmic derivative, which is the case `j = 1` of the relative
derivative bounds of `HairpinRelativeDerivatives.lean`, and the bounded shift
`|s - x(s)| ≤ A²M/2`, which follows from the estimate of `HairpinPulseDecay.lean`
— and concludes.

Main results:

* `HairpinRelative.abs_frontArclength_sub_le` : `|σ(u) - u| ≤ A²M/2`;
* `HairpinRelative.hairpin_curv_ge_pulse` : `K_*(s) ≥ b₀ y(s)` with `b₀ > 0`.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ} {A M : ℝ}

/-- **The bounded shift between the two arclengths.** -/
theorem abs_frontArclength_sub_le (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) (u : ℝ) :
    |frontArclength f theta u - u| ≤ A ^ 2 * M / 2 := by
  have hderiv := hasDerivAt_frontArclength hf hfpos hthetac
  have hge : ∀ t, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta t) ^ 2) := by
    intro t
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta t) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta t))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rcases le_or_gt 0 u with hu | hu
  · have h1 : u ≤ frontArclength f theta u := by
      have := ArclengthInverse.le_of_deriv_ge (c := 1) hderiv hge hu
      rw [frontArclength_zero] at this
      linarith
    have h2 := frontArclength_le hf hfpos hthetac hmem hdecay hM hu
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ frontArclength f theta u - u)]
    linarith
  · have h1 : frontArclength f theta u ≤ u := by
      have := ArclengthInverse.ge_of_deriv_ge (c := 1) hderiv hge hu.le
      rw [frontArclength_zero] at this
      linarith
    have h2 := le_frontArclength hf hfpos hthetac hmem hdecay hM hu.le
    rw [abs_of_nonpos (by linarith : frontArclength f theta u - u ≤ 0)]
    linarith

/-- The curvature of the hairpin is positive. -/
theorem curvField_pos (hfpos : ∀ t, 0 < f t) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    0 < curvField f t :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) (hfpos t)

/-- **The lower comparison `K_* ≥ b₀ y` for the hairpin.**  There is `b₀ > 0`
such that the curvature at the arclength value `s` dominates `b₀` times the
steering pulse at the same value. -/
theorem hairpin_curv_ge_pulse (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (b₀ : ℝ) (theta x : ℝ → ℝ), 0 < b₀ ∧ (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      ∀ s, b₀ * pulseField f (theta (x s)) ≤ curvField f (theta s) := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hMpos : 0 < f t₁ := hfpos t₁
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ f t₁ := fun t ht => hmax ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, -, -, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hdecay : ∀ u, curvField f (theta u) ≤ (2 / f t₀) * Real.exp (-|u| / f t₁) := fun u =>
    HairpinArclength.curvature_decay_arclength hcontf.continuousOn hm hlow hup hmem hval u
  obtain ⟨x, hxinv, -, -⟩ := exists_pulseState hf hfpos hmem' hderiv'
  -- the curvature and its logarithmic derivative
  set K : ℝ → ℝ := fun u => curvField f (theta u) with hK
  have hKpos : ∀ u, 0 < K u := fun u => curvField_pos hfpos (hmem u)
  have hKdiff : ∀ u, HasDerivAt K (deriv K u) u := by
    intro u
    have h : DifferentiableAt ℝ K u :=
      (((contDiff_curvField hf hfpos).differentiable (by simp)).differentiableAt).comp u
        (hderiv' u).differentiableAt
    exact h.hasDerivAt
  obtain ⟨C, hC0, hC⟩ := abs_iteratedDeriv_curv_le hf hfpos hmem' hderiv' 1
  have hCbound : ∀ u, |deriv K u / K u| ≤ C := by
    intro u
    have h1 : |deriv K u| ≤ C * K u := by
      have := hC u
      rwa [iteratedDeriv_one] at this
    rw [abs_div, abs_of_pos (hKpos u), div_le_iff₀ (hKpos u)]
    exact h1
  have hlog : ∀ u, HasDerivAt (fun r => Real.log (K r)) (deriv K u / K u) u := fun u =>
    (hKdiff u).log (hKpos u).ne'
  -- the bounded shift
  have hshift : ∀ s, |s - x s| ≤ (2 / f t₀) ^ 2 * f t₁ / 2 := by
    intro s
    have h := abs_frontArclength_sub_le hf hfpos hthetac hmem' hdecay hMpos (x s)
    rwa [hxinv s] at h
  -- the exact identity `K(x s) = y s / c s`
  set c : ℝ → ℝ := fun s => 1 / Real.sqrt (1 + curvField f (theta (x s)) ^ 2) with hc
  have hsqrtpos : ∀ s, 0 < Real.sqrt (1 + curvField f (theta (x s)) ^ 2) := fun s =>
    sqrt_one_add_sq_pos _
  have hc0 : ∀ s, 0 < c s := fun s => by
    rw [hc]; exact div_pos one_pos (hsqrtpos s)
  have hc1 : ∀ s, c s ≤ 1 := by
    intro s
    have h1 : (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta (x s)) ^ 2) := by
      have h : (1:ℝ) ≤ 1 + curvField f (theta (x s)) ^ 2 := by
        nlinarith [sq_nonneg (curvField f (theta (x s)))]
      calc (1:ℝ) = Real.sqrt 1 := by simp
        _ ≤ _ := Real.sqrt_le_sqrt h
    rw [hc, div_le_one (hsqrtpos s)]
    exact h1
  have hid : ∀ s, K (x s) = pulseField f (theta (x s)) / c s := by
    intro s
    rw [hc, pulseField, hK]
    field_simp
  have hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)) := fun s => pulseField_nonneg hfpos (hmem' _)
  refine ⟨Real.exp (-C * ((2 / f t₀) ^ 2 * f t₁ / 2)), theta, x, Real.exp_pos _, hmem, hval,
    hxinv, fun s => ?_⟩
  exact HairpinMass.Kstar_lower_bound hKpos hlog hCbound hC0 hshift hy0 hc0 hc1 hid s

/-! ### A worked instance

The hypotheses are consistent: the constant profile `f ≡ 2` is smooth and
positive on the line. -/

example : ∃ b₀ : ℝ, 0 < b₀ := by
  obtain ⟨b₀, -, -, hb, -⟩ :=
    hairpin_curv_ge_pulse (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨b₀, hb⟩

end HairpinRelative
