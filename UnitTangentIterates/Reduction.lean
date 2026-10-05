module

public import UnitTangentIterates.Defs

/-!
# Directional widths along unit-tangent orbits, and noncircularity

This file isolates the geometric part of the last step of the proof of Theorem 1.1.

* `Ovals.coord_le_unitTangentTransform`: the unit-tangent transform can only push a closed
  curve outward.  At a point where the coordinate in direction `v` is maximal, the tangent is
  orthogonal to `v`, so `𝒯γ` has the same coordinate there.  Consequently the width of a rear
  curve in any direction is at most the width of its front (`Ovals.width_le_of_unitTangent`):
  backward iterates of a thin curve stay thin.
* `Ovals.norm_unitTangentTransform_sub_center`: `𝒯` maps a regular curve lying on a circle of
  radius `r` to a curve lying on the concentric circle of radius `√(r² + 1)`.
* `Ovals.not_isCircle_of_iterates_width_le`: if all iterates `𝒯ⁿ Γ` are ovals and each has
  width at most `W` in some direction, then `Γ` is not a circle (the radii of the iterates of
  a circle grow like `√n`).
-/

@[expose] public section

namespace Ovals

open Complex Real

/-- The coordinate of `z` in direction `v`. -/
noncomputable def coord (v z : ℂ) : ℝ := (z * (starRingEnd ℂ) v).re

lemma coord_add (v a b : ℂ) : coord v (a + b) = coord v a + coord v b := by
  simp [coord, add_mul]

lemma coord_sub (v a b : ℂ) : coord v (a - b) = coord v a - coord v b := by
  simp [coord, sub_mul]

lemma coord_neg_dir (v z : ℂ) : coord (-v) z = - coord v z := by
  simp [coord]

/-- A continuous periodic function attains a global maximum. -/
lemma exists_max_of_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : Continuous f)
    (hper : Function.Periodic f p) : ∃ t₀, ∀ t, f t ≤ f t₀ := by
  obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := p)).exists_isMaxOn
    (Set.nonempty_Icc.2 hp.le) hf.continuousOn
  refine ⟨t₀, fun t => ?_⟩
  have h1 : f t = f (toIcoMod hp 0 t) := by
    rw [← hper.sub_zsmul_eq (toIcoDiv hp 0 t)]; rfl
  rw [h1]
  apply ht₀
  have := toIcoMod_mem_Ico hp 0 t
  simp only [zero_add] at this
  exact ⟨this.1, this.2.le⟩

/-- At a maximum of the coordinate in direction `v`, the velocity is orthogonal to `v`. -/
lemma coord_deriv_eq_zero_of_max {γ : ℝ → ℂ} {v : ℂ} {t₀ : ℝ} (hγ : DifferentiableAt ℝ γ t₀)
    (hmax : ∀ t, coord v (γ t) ≤ coord v (γ t₀)) : coord v (deriv γ t₀) = 0 := by
  have hd : HasDerivAt (fun t => coord v (γ t)) (coord v (deriv γ t₀)) t₀ := by
    have h1 : HasDerivAt (fun t => γ t * (starRingEnd ℂ) v) (deriv γ t₀ * (starRingEnd ℂ) v) t₀ :=
      hγ.hasDerivAt.mul_const _
    have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ h1)
    exact h2
  exact (IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmax) hd)

lemma coord_div_real (v z : ℂ) (a : ℝ) : coord v (z / (a : ℂ)) = coord v z / a := by
  simp [coord, div_mul_eq_mul_div, Complex.div_ofReal_re]

/-- **`𝒯` pushes outward.**  For a differentiable periodic curve `γ` and a direction `v`,
the maximum of the `v`-coordinate along `γ` is attained at a parameter `t₀` where `𝒯γ` has the
same coordinate. -/
theorem coord_le_unitTangentTransform {γ : ℝ → ℂ} {p : ℝ} (hp : 0 < p) (hγ : Differentiable ℝ γ)
    (hper : Function.Periodic γ p) (v : ℂ) :
    ∃ t₀, (∀ t, coord v (γ t) ≤ coord v (γ t₀)) ∧
      coord v (unitTangentTransform γ t₀) = coord v (γ t₀) := by
  obtain ⟨t₀, ht₀⟩ := exists_max_of_periodic hp
    (show Continuous fun t => coord v (γ t) from
      Complex.continuous_re.comp (hγ.continuous.mul continuous_const))
    (fun t => by simp only [hper t])
  refine ⟨t₀, ht₀, ?_⟩
  have h0 := coord_deriv_eq_zero_of_max (hγ t₀) ht₀
  simp only [unitTangentTransform, coord_add, coord_div_real, h0, zero_div, add_zero]

/-- **Rears are no wider than fronts.**  If `𝒯γ` lies in a strip of width `W` orthogonal to
`v`, so does the differentiable periodic curve `γ`. -/
theorem width_le_of_unitTangent {γ : ℝ → ℂ} {p : ℝ} (hp : 0 < p) (hγ : Differentiable ℝ γ)
    (hper : Function.Periodic γ p) {v : ℂ} {W : ℝ}
    (hW : ∀ t t', coord v (unitTangentTransform γ t - unitTangentTransform γ t') ≤ W) :
    ∀ t t', coord v (γ t - γ t') ≤ W := by
  obtain ⟨t₀, h₀, e₀⟩ := coord_le_unitTangentTransform hp hγ hper v
  obtain ⟨t₁, h₁, e₁⟩ := coord_le_unitTangentTransform hp hγ hper (-v)
  intro t t'
  have := hW t₀ t₁
  simp only [coord_sub, coord_neg_dir] at *
  have a := h₀ t
  have b := h₁ t'
  linarith

/-- Widths along an orbit: if `𝒯ᴺγ` lies in a strip of width `W` and the iterates are
differentiable and `p`-periodic, then every earlier iterate lies in the same strip. -/
theorem width_le_of_iterate {γ : ℝ → ℂ} {p : ℝ} (hp : 0 < p) {N : ℕ}
    (hdiff : ∀ n, Differentiable ℝ (unitTangentTransform^[n] γ))
    (hper : ∀ n, Function.Periodic (unitTangentTransform^[n] γ) p) {v : ℂ} {W : ℝ}
    (hW : ∀ t t', coord v (unitTangentTransform^[N] γ t - unitTangentTransform^[N] γ t') ≤ W) :
    ∀ n ≤ N, ∀ t t', coord v (unitTangentTransform^[n] γ t - unitTangentTransform^[n] γ t') ≤ W := by
  intro n hn
  induction hn using Nat.decreasingInduction with
  | self => exact hW
  | of_succ k hk ih =>
    apply width_le_of_unitTangent hp (hdiff k) (hper k)
    simpa [← Function.iterate_succ_apply' unitTangentTransform k γ] using ih

/-- `𝒯` maps a regular curve on the circle `‖z - c‖ = r` to the circle of radius `√(r²+1)`. -/
theorem norm_unitTangentTransform_sub_center {γ : ℝ → ℂ} {c : ℂ} {r : ℝ}
    (hγ : Differentiable ℝ γ) (hreg : ∀ t, deriv γ t ≠ 0) (hc : ∀ t, ‖γ t - c‖ = r) (t : ℝ) :
    ‖unitTangentTransform γ t - c‖ ^ 2 = r ^ 2 + 1 := by
  -- the derivative of `‖γ - c‖²` vanishes
  have hconst : HasDerivAt (fun t => ‖γ t - c‖ ^ 2) 0 t := by
    have : (fun t => ‖γ t - c‖ ^ 2) = fun _ => r ^ 2 := funext fun t => by rw [hc]
    rw [this]; exact hasDerivAt_const _ _
  have hd : HasDerivAt (fun t => ‖γ t - c‖ ^ 2)
      (2 * ((γ t - c) * (starRingEnd ℂ) (deriv γ t)).re) t := by
    have h1 : HasDerivAt (fun t => γ t - c) (deriv γ t) t :=
      (hγ t).hasDerivAt.sub_const c
    have h2 := h1.norm_sq
    convert h2 using 1
    simp; ring
  have horth : ((γ t - c) * (starRingEnd ℂ) (deriv γ t)).re = 0 := by
    have := hconst.unique hd; linarith
  set a := γ t - c
  set w := deriv γ t
  have hw : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 (hreg t)
  have hsplit : unitTangentTransform γ t - c = a + w / (‖w‖ : ℂ) := by
    simp only [unitTangentTransform, a, w]; ring
  rw [hsplit, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hc t]
  have hu : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw]
  have hre : (a * (starRingEnd ℂ) (w / (‖w‖ : ℂ))).re = 0 := by
    rw [map_div₀, Complex.conj_ofReal, mul_div_assoc', Complex.div_ofReal_re, horth, zero_div]
  rw [hu, hre]; ring

/-- On a circle of radius `R`, a regular differentiable periodic curve reaches the point
`c + R v` in every unit direction `v`. -/
theorem exists_eq_center_add_of_circle {γ : ℝ → ℂ} {c v : ℂ} {R p : ℝ} (hp : 0 < p)
    (hγ : Differentiable ℝ γ) (hper : Function.Periodic γ p) (hreg : ∀ t, deriv γ t ≠ 0)
    (hc : ∀ t, ‖γ t - c‖ = R) (hv : ‖v‖ = 1) : ∃ t₀, coord v (γ t₀ - c) = R := by
  obtain ⟨t₀, ht₀⟩ := exists_max_of_periodic hp
    (show Continuous fun t => coord v (γ t) from
      Complex.continuous_re.comp (hγ.continuous.mul continuous_const))
    (fun t => by simp only [hper t])
  have h0 := coord_deriv_eq_zero_of_max (hγ t₀) ht₀
  -- the derivative is also orthogonal to the radius
  have hconst : HasDerivAt (fun t => ‖γ t - c‖ ^ 2) 0 t₀ := by
    have : (fun t => ‖γ t - c‖ ^ 2) = fun _ => R ^ 2 := funext fun t => by rw [hc]
    rw [this]; exact hasDerivAt_const _ _
  have hd : HasDerivAt (fun t => ‖γ t - c‖ ^ 2)
      (2 * ((γ t₀ - c) * (starRingEnd ℂ) (deriv γ t₀)).re) t₀ := by
    have h1 : HasDerivAt (fun t => γ t - c) (deriv γ t₀) t₀ :=
      (hγ t₀).hasDerivAt.sub_const c
    convert h1.norm_sq using 1
    simp; ring
  have horth : ((γ t₀ - c) * (starRingEnd ℂ) (deriv γ t₀)).re = 0 := by
    have := hconst.unique hd; linarith
  -- hence the radius is parallel to `v`, so its `v`-coordinate is `± R`
  set a := γ t₀ - c
  set w := deriv γ t₀
  have hw : w ≠ 0 := hreg t₀
  have hvw : (v * (starRingEnd ℂ) w).re = 0 := by
    have : (w * (starRingEnd ℂ) v).re = 0 := h0
    have e : v * (starRingEnd ℂ) w = (starRingEnd ℂ) (w * (starRingEnd ℂ) v) := by simp [mul_comm]
    rw [e, Complex.conj_re, this]
  have hR : 0 ≤ R := by rw [← hc 0]; exact norm_nonneg _
  have hsq : coord v a ^ 2 = R ^ 2 := by
    have haw : a.re * w.re + a.im * w.im = 0 := by
      simpa [Complex.mul_re] using horth
    have hvw' : v.re * w.re + v.im * w.im = 0 := by
      simpa [Complex.mul_re] using hvw
    have hX1 : (a.re * v.im - a.im * v.re) * w.re = 0 := by linear_combination v.im * haw - a.im * hvw'
    have hX2 : (a.re * v.im - a.im * v.re) * w.im = 0 := by
      linear_combination -v.re * haw + a.re * hvw'
    have hX : a.re * v.im - a.im * v.re = 0 := by
      by_contra hne
      apply hw
      apply Complex.ext
      · simpa using (mul_eq_zero.1 hX1).resolve_left hne
      · simpa using (mul_eq_zero.1 hX2).resolve_left hne
    have hnv : v.re ^ 2 + v.im ^ 2 = 1 := by
      have := congrArg (· ^ 2) hv
      simp only [one_pow] at this
      rw [← this, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hna : a.re ^ 2 + a.im ^ 2 = R ^ 2 := by
      rw [← hc t₀, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have : coord v a = a.re * v.re + a.im * v.im := by simp [coord, Complex.mul_re]
    rw [this]
    linear_combination (a.re ^ 2 + a.im ^ 2) * hnv + hna - (a.re * v.im - a.im * v.re) * hX
  have hcases : coord v a = R ∨ coord v a = -R := by
    have := sq_eq_sq_iff_eq_or_eq_neg.1 hsq
    exact this
  rcases hcases with h | h
  · exact ⟨t₀, h⟩
  · -- the maximal coordinate is `-R`, so the curve is constant `c - R v`
    exfalso
    have hall : ∀ t, γ t = c - (R : ℂ) * v := by
      intro t
      have hle : coord v (γ t - c) ≤ -R := by
        have := ht₀ t
        rw [coord_sub] at h ⊢; linarith
      have : ‖(γ t - c) + (R : ℂ) * v‖ ^ 2 ≤ 0 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq, hc t, norm_mul, hv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hR]
        have : ((γ t - c) * (starRingEnd ℂ) ((R : ℂ) * v)).re = R * coord v (γ t - c) := by
          simp [coord, Complex.conj_ofReal]; ring
        rw [this]; nlinarith
      have h0 : (γ t - c) + (R : ℂ) * v = 0 := by
        have := sq_nonneg ‖(γ t - c) + (R : ℂ) * v‖
        exact norm_eq_zero.1 (by nlinarith [norm_nonneg ((γ t - c) + (R : ℂ) * v)])
      linear_combination h0
    have : deriv γ t₀ = 0 := by
      rw [show γ = fun _ => c - (R : ℂ) * v from funext hall]; simp
    exact hw this

/-- **Iterates of a circle grow.**  If `Γ` lies on the circle `‖z - c‖ = r` and its iterates
`𝒯ⁿ Γ` are smooth regular curves, then `𝒯ⁿ Γ` lies on the circle of radius `√(r² + n)`. -/
theorem norm_iterate_sub_center_sq {Γ : ℝ → ℂ} {c : ℂ} {r : ℝ} (hc : ∀ t, ‖Γ t - c‖ = r)
    (hit : ∀ n, IsOval (unitTangentTransform^[n] Γ)) (n : ℕ) (t : ℝ) :
    ‖unitTangentTransform^[n] Γ t - c‖ ^ 2 = r ^ 2 + n := by
  induction n generalizing t with
  | zero => simp [hc]
  | succ k ih =>
    have hr : 0 ≤ r ^ 2 + k := by positivity
    rw [Function.iterate_succ_apply']
    have hk := hit k
    have := norm_unitTangentTransform_sub_center (c := c) (r := Real.sqrt (r ^ 2 + k))
      (hk.contDiff.differentiable (by simp)) hk.regular
      (fun t => by rw [← Real.sqrt_sq (norm_nonneg _), ih t]) t
    rw [this, Real.sq_sqrt hr]; push_cast; ring

/-- **Noncircularity from bounded widths.**  If every iterate `𝒯ⁿ Γ` is an oval and lies in a
strip of width `W` (in a direction that may depend on `n`), then `Γ` is not a circle. -/
theorem not_isCircle_of_iterates_width_le {Γ : ℝ → ℂ} {W : ℝ}
    (hit : ∀ n, IsOval (unitTangentTransform^[n] Γ))
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ t t',
      coord v (unitTangentTransform^[n] Γ t - unitTangentTransform^[n] Γ t') ≤ W) :
    ¬ IsCircle Γ := by
  rintro ⟨c, r, hc⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (W ^ 2)
  obtain ⟨v, hv, hWn⟩ := hW n
  set γ := unitTangentTransform^[n] Γ
  have hγ := hit n
  obtain ⟨p, hp, hper, -⟩ := hγ.closed_simple
  have hdiff : Differentiable ℝ γ := hγ.contDiff.differentiable (by simp)
  set R := Real.sqrt (r ^ 2 + n)
  have hcR : ∀ t, ‖γ t - c‖ = R := fun t => by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_iterate_sub_center_sq hc hit n t]
  obtain ⟨t₀, h₀⟩ := exists_eq_center_add_of_circle hp hdiff hper hγ.regular hcR hv
  obtain ⟨t₁, h₁⟩ := exists_eq_center_add_of_circle hp hdiff hper hγ.regular hcR
    (v := -v) (by rw [norm_neg, hv])
  have hw := hWn t₀ t₁
  rw [coord_neg_dir] at h₁
  have e : γ t₀ - γ t₁ = (γ t₀ - c) - (γ t₁ - c) := by ring
  rw [e, coord_sub] at hw
  have hRW : 2 * R ≤ W := by linarith
  have hRn : (n : ℝ) ≤ R ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]; nlinarith [sq_nonneg r]
  nlinarith [Real.sqrt_nonneg (r ^ 2 + n)]

end Ovals

end
