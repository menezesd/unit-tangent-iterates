import Mathlib

/-!
# Mass, defect and lower comparison for the hairpin pulse

This file formalizes the remaining self-contained computations of the lemma
*Hairpin pulse estimates* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*, namely the identities and inequalities of its last two
paragraphs.

* the steering pulse in terms of the curvature,
  `y = K_*/√(1+K_*²)`, `c = 1/√(1+K_*²)`;
* the exact mass identity `y(s) ds = K_*(u) du`, in the integrated form
  `∫_{σ(a)}^{σ(b)} y = ∫_a^b K_*`, which turns the total turning `π` of the
  rear tangent into `∫_ℝ y = π`;
* the defect integrand estimate `0 ≤ 1 - c ≤ y²`, which makes
  `Δ = ∫(1-c)` finite;
* the bounded-shift Harnack inequality
  `K_*(s) ≥ e^{-C|s-t|} K_*(t)` coming from `|(log K_*)'| ≤ C`, and the
  resulting lower comparison `K_* ≥ b₀ y`.

Main results:

* `sin_cos_of_tan_eq` : `y` and `c` from the curvature;
* `mass_identity` : the exact mass identity;
* `defect_integrand_le` : `0 ≤ 1 - √(1-y²) ≤ y²`;
* `harnack_of_log_deriv_bounded` : the bounded-shift Harnack inequality;
* `Kstar_lower_bound` : `K_*(s) ≥ b₀ y(s)`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral Set

namespace HairpinMass

/-! ### The steering pulse in terms of the curvature -/

/-- **The steering pulse from the curvature.**  If the steering angle is
`δ = arctan K` then `sin δ = K/√(1+K²)` and `cos δ = 1/√(1+K²)`. -/
theorem sin_cos_of_tan_eq (K : ℝ) :
    Real.sin (Real.arctan K) = K / Real.sqrt (1 + K ^ 2) ∧
      Real.cos (Real.arctan K) = 1 / Real.sqrt (1 + K ^ 2) :=
  ⟨Real.sin_arctan K, Real.cos_arctan K⟩

/-! ### The mass identity -/

/-- **The mass identity.**  With front arclength `σ` satisfying
`σ' = √(1 + K²)` and the pulse given by `y(σ(u)) = K(u)/√(1+K(u)²)`, the
steering mass of the front equals the total turning of the rear:
`∫_{σ(a)}^{σ(b)} y(s) ds = ∫_a^b K(u) du`. -/
theorem mass_identity {K sigma y : ℝ → ℝ} {a b : ℝ}
    (hsig : ∀ u ∈ uIcc a b, HasDerivAt sigma (Real.sqrt (1 + K u ^ 2)) u)
    (hK : Continuous K) (hy : Continuous y)
    (hyK : ∀ u, y (sigma u) = K u / Real.sqrt (1 + K u ^ 2)) :
    (∫ s in (sigma a)..(sigma b), y s) = ∫ u in a..b, K u := by
  have hcont : ContinuousOn (fun u => Real.sqrt (1 + K u ^ 2)) (uIcc a b) := by
    fun_prop
  have hchange : (∫ u in a..b, Real.sqrt (1 + K u ^ 2) * y (sigma u))
      = ∫ s in (sigma a)..(sigma b), y s := by
    simpa [Function.comp, smul_eq_mul] using
      intervalIntegral.integral_comp_smul_deriv (f := sigma)
        (f' := fun u => Real.sqrt (1 + K u ^ 2)) (g := y) hsig hcont hy
  rw [← hchange]
  refine intervalIntegral.integral_congr ?_
  intro u _
  have hpos : 0 < Real.sqrt (1 + K u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only
  rw [hyK u]
  field_simp

/-! ### The defect integrand -/

/-- **The defect integrand.**  With `c = √(1 - y²)` and `|y| ≤ 1`, the
integrand of the perimeter defect satisfies `0 ≤ 1 - c ≤ y²`. -/
theorem defect_integrand_le {y : ℝ} (hy : |y| ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - y ^ 2) ∧ 1 - Real.sqrt (1 - y ^ 2) ≤ y ^ 2 := by
  have hy2 : y ^ 2 ≤ 1 := by
    have := abs_le.mp hy
    nlinarith
  have h0 : 0 ≤ 1 - y ^ 2 := by linarith
  have hle1 : Real.sqrt (1 - y ^ 2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - y ^ 2 ≤ 1 by nlinarith [sq_nonneg y])
    rwa [Real.sqrt_one] at h
  refine ⟨by linarith, ?_⟩
  have hsq : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]

/-! ### The bounded-shift Harnack inequality -/

/-- **The bounded-shift Harnack inequality.**  If the logarithmic derivative of
a positive function is bounded by `C`, then `K(s) ≥ e^{-C|s-t|} K(t)`. -/
theorem harnack_of_log_deriv_bounded {K L : ℝ → ℝ} {C : ℝ}
    (hpos : ∀ u, 0 < K u)
    (hlog : ∀ u, HasDerivAt (fun r => Real.log (K r)) (L u) u)
    (hb : ∀ u, |L u| ≤ C) (s t : ℝ) :
    Real.exp (-C * |s - t|) * K t ≤ K s := by
  have hderiv : ∀ u ∈ uIcc t s,
      HasDerivWithinAt (fun r => Real.log (K r)) (L u) (uIcc t s) u := fun u _ =>
    (hlog u).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc t s, ‖L u‖ ≤ C := fun u _ => by
    simpa [Real.norm_eq_abs] using hb u
  have hmvt := (convex_uIcc t s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have habs : |Real.log (K s) - Real.log (K t)| ≤ C * |s - t| := by
    simpa [Real.norm_eq_abs] using hmvt
  have hlow : Real.log (K t) - C * |s - t| ≤ Real.log (K s) := by
    have := (abs_le.mp habs).1
    linarith
  have hkey := Real.exp_le_exp.mpr hlow
  rw [Real.exp_sub, Real.exp_log (hpos t), Real.exp_log (hpos s)] at hkey
  have heq : Real.exp (-C * |s - t|) * K t = K t / Real.exp (C * |s - t|) := by
    rw [neg_mul, Real.exp_neg]
    field_simp
  rw [heq]
  exact hkey

/-- **The lower comparison `K_* ≥ b₀ y`.**  The exact identity
`K_*(x(s)) = y(s)/c(s)`, the bounded shift `|s - x(s)| ≤ D` and the Harnack
inequality give `K_*(s) ≥ e^{-CD} y(s)`. -/
theorem Kstar_lower_bound {K L y c x : ℝ → ℝ} {C D : ℝ}
    (hpos : ∀ u, 0 < K u)
    (hlog : ∀ u, HasDerivAt (fun r => Real.log (K r)) (L u) u)
    (hb : ∀ u, |L u| ≤ C) (hC : 0 ≤ C)
    (hshift : ∀ s, |s - x s| ≤ D)
    (hy0 : ∀ s, 0 ≤ y s) (hc0 : ∀ s, 0 < c s) (hc1 : ∀ s, c s ≤ 1)
    (hid : ∀ s, K (x s) = y s / c s) (s : ℝ) :
    Real.exp (-C * D) * y s ≤ K s := by
  have h1 : Real.exp (-C * |s - x s|) * K (x s) ≤ K s :=
    harnack_of_log_deriv_bounded hpos hlog hb s (x s)
  have h2 : Real.exp (-C * D) ≤ Real.exp (-C * |s - x s|) :=
    Real.exp_le_exp.mpr (by nlinarith [hshift s, abs_nonneg (s - x s)])
  have h3 : y s ≤ K (x s) := by
    rw [hid s]
    rw [le_div_iff₀ (hc0 s)]
    nlinarith [hy0 s, hc1 s, hc0 s]
  have h4 : Real.exp (-C * D) * y s ≤ Real.exp (-C * |s - x s|) * K (x s) :=
    mul_le_mul h2 h3 (hy0 s) (Real.exp_pos _).le
  linarith

end HairpinMass
