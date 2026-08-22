import Mathlib

/-!
# A uniform bound from an `L¹` bound and a derivative bound

The theorem *Curvature-measure matching* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* compares two curvatures in `L¹`: it bounds
`∫_{J_H}|k_H − K_P|`.  The stability estimates of `CurvatureStability.lean`,
which turn a comparison of curvatures into a comparison of the curves
themselves in the metric of the space of marked curves, consume a **uniform**
bound `|k₁ − k₂| ≤ ε` instead.  This file supplies the elementary interpolation
between the two.

If `u` is differentiable with `|u'| ≤ M` and `∫_c^{c+P}|u| ≤ ε`, then a large
value `m = |u(x₀)|` at some point of the window forces `|u| ≥ m − M|t − x₀|` on
a whole neighbourhood of `x₀`, and integrating that tent over the side of `x₀`
which has room inside the window gives `mℓ − Mℓ²/2 ≤ ε` with
`ℓ = min(m/M, P/2)`.  Both branches of the minimum then bound `m`:

`|u(x₀)| ≤ max(√(2Mε), 4ε/P)`  (`SupFromL1.abs_le_of_intervalIntegral_abs_le`).

Only the mean value inequality and monotonicity of the integral are used; no
periodicity is assumed.
-/

noncomputable section

open Set

namespace SupFromL1

/-! ### The tent lower bound -/

/-- **A differentiable function with bounded derivative dominates a tent.**  If
`|u'| ≤ M` then `|u t| ≥ |u x₀| − M|t − x₀|` for every `t`. -/
theorem tent_le_abs {u u' : ℝ → ℝ} {M : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hbd : ∀ x, |u' x| ≤ M) (x0 t : ℝ) :
    |u x0| - M * |t - x0| ≤ |u t| := by
  have hderiv : ∀ r ∈ uIcc x0 t, HasDerivWithinAt u (u' r) (uIcc x0 t) r :=
    fun r _ => (hu r).hasDerivWithinAt
  have hnorm : ∀ r ∈ uIcc x0 t, ‖u' r‖ ≤ M := fun r _ => by
    simpa [Real.norm_eq_abs] using hbd r
  have hmvt := (convex_uIcc x0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hnorm Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have h1 : |u x0| - |u t| ≤ |u t - u x0| := by
    have := abs_sub_abs_le_abs_sub (u x0) (u t)
    rwa [abs_sub_comm (u x0) (u t)] at this
  linarith

/-! ### The tent integral inside the window -/

/-- **The integral of the tent over a subinterval is at most the `L¹` bound.** -/
theorem integral_tent_le {u u' : ℝ → ℝ} {c P M eps p q x0 : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hbd : ∀ x, |u' x| ≤ M)
    (hp : c ≤ p) (hpq : p ≤ q) (hq : q ≤ c + P)
    (hint : (∫ x in c..(c + P), |u x|) ≤ eps) :
    (∫ t in p..q, (|u x0| - M * |t - x0|)) ≤ eps := by
  have hdiff : Differentiable ℝ u := fun x => (hu x).differentiableAt
  have habs : Continuous fun t => |u t| := hdiff.continuous.abs
  have hten : Continuous fun t : ℝ => |u x0| - M * |t - x0| :=
    continuous_const.sub (continuous_const.mul ((continuous_id.sub continuous_const).abs))
  have hmono : (∫ t in p..q, (|u x0| - M * |t - x0|)) ≤ ∫ t in p..q, |u t| :=
    intervalIntegral.integral_mono_on hpq (hten.intervalIntegrable _ _)
      (habs.intervalIntegrable _ _) (fun t _ => tent_le_abs hu hbd x0 t)
  have hsplit1 : (∫ x in c..p, |u x|) + (∫ x in p..(c + P), |u x|)
      = ∫ x in c..(c + P), |u x| :=
    intervalIntegral.integral_add_adjacent_intervals (habs.intervalIntegrable _ _)
      (habs.intervalIntegrable _ _)
  have hsplit2 : (∫ x in p..q, |u x|) + (∫ x in q..(c + P), |u x|)
      = ∫ x in p..(c + P), |u x| :=
    intervalIntegral.integral_add_adjacent_intervals (habs.intervalIntegrable _ _)
      (habs.intervalIntegrable _ _)
  have h1 : 0 ≤ ∫ x in c..p, |u x| :=
    intervalIntegral.integral_nonneg hp (fun x _ => abs_nonneg _)
  have h2 : 0 ≤ ∫ x in q..(c + P), |u x| :=
    intervalIntegral.integral_nonneg hq (fun x _ => abs_nonneg _)
  linarith

/-! ### The two sides -/

/-- The area of a tent of height `m` and slope `M` over a base of length `l`. -/
theorem integral_affine (m M l : ℝ) :
    (∫ s in (0:ℝ)..l, (m - M * s)) = m * l - M * l ^ 2 / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => m) MeasureTheory.volume 0 l :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s : ℝ => M * s) MeasureTheory.volume 0 l :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- The tent integrated over the right-hand side of its apex. -/
theorem integral_tent_right (m M x0 l : ℝ) (hl : 0 ≤ l) :
    (∫ t in x0..(x0 + l), (m - M * |t - x0|)) = m * l - M * l ^ 2 / 2 := by
  have hcongr : (∫ t in x0..(x0 + l), (m - M * |t - x0|))
      = ∫ t in x0..(x0 + l), (m - M * (t - x0)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le (by linarith : x0 ≤ x0 + l)] at ht
    show m - M * |t - x0| = m - M * (t - x0)
    rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - x0)]
  have hsub : (∫ t in x0..(x0 + l), (m - M * (t - x0))) = ∫ s in (0:ℝ)..l, (m - M * s) := by
    have := intervalIntegral.integral_comp_sub_right (a := x0) (b := x0 + l)
      (fun s => m - M * s) x0
    simpa using this
  rw [hcongr, hsub, integral_affine]

/-- The tent integrated over the left-hand side of its apex. -/
theorem integral_tent_left (m M x0 l : ℝ) (hl : 0 ≤ l) :
    (∫ t in (x0 - l)..x0, (m - M * |t - x0|)) = m * l - M * l ^ 2 / 2 := by
  have hcongr : (∫ t in (x0 - l)..x0, (m - M * |t - x0|))
      = ∫ t in (x0 - l)..x0, (m - M * (x0 - t)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le (by linarith : x0 - l ≤ x0)] at ht
    show m - M * |t - x0| = m - M * (x0 - t)
    rw [abs_of_nonpos (by linarith [ht.2] : t - x0 ≤ (0:ℝ))]
    ring
  have hrefl : (∫ t in (x0 - l)..x0, (m - M * (x0 - t))) = ∫ s in (0:ℝ)..l, (m - M * s) := by
    have h := intervalIntegral.integral_comp_sub_left (a := x0 - l) (b := x0)
      (fun s => m - M * s) x0
    simpa using h
  rw [hcongr, hrefl, integral_affine]

/-! ### The interpolation -/

/-- **The key inequality.**  With `m = |u x₀|` and any `ℓ ≤ P/2`, the tent of
height `m` and slope `M` fits inside the window on at least one side of `x₀`,
so `mℓ − Mℓ²/2 ≤ ε`. -/
theorem tent_area_le {u u' : ℝ → ℝ} {c P M eps x0 : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hbd : ∀ x, |u' x| ≤ M)
    (hint : (∫ x in c..(c + P), |u x|) ≤ eps) (hx0 : x0 ∈ Icc c (c + P))
    {l : ℝ} (hl0 : 0 ≤ l) (hlP : l ≤ P / 2) :
    |u x0| * l - M * l ^ 2 / 2 ≤ eps := by
  obtain ⟨hc1, hc2⟩ := hx0
  by_cases hside : x0 + P / 2 ≤ c + P
  · have hq : x0 + l ≤ c + P := by linarith
    have h := integral_tent_le (u := u) (u' := u') (c := c) (P := P) (M := M)
      (p := x0) (q := x0 + l) (x0 := x0) hu hbd hc1 (by linarith) hq hint
    rwa [integral_tent_right (|u x0|) M x0 l hl0] at h
  · push_neg at hside
    have hp : c ≤ x0 - l := by linarith
    have h := integral_tent_le (u := u) (u' := u') (c := c) (P := P) (M := M)
      (p := x0 - l) (q := x0) (x0 := x0) hu hbd hp (by linarith) hc2 hint
    rwa [integral_tent_left (|u x0|) M x0 l hl0] at h

/-- **A uniform bound from an `L¹` bound and a derivative bound.**  If `u` is
differentiable with `|u'| ≤ M` and `∫_c^{c+P}|u| ≤ ε`, then on the whole window
`|u| ≤ max(√(2Mε), 4ε/P)`. -/
theorem abs_le_of_intervalIntegral_abs_le {u u' : ℝ → ℝ} {c P M eps x0 : ℝ}
    (hP : 0 < P) (hM : 0 < M) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hbd : ∀ x, |u' x| ≤ M) (hint : (∫ x in c..(c + P), |u x|) ≤ eps)
    (hx0 : x0 ∈ Icc c (c + P)) :
    |u x0| ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) := by
  have heps : 0 ≤ eps := le_trans
    (intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)) hint
  set m : ℝ := |u x0| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  rcases eq_or_lt_of_le hm0 with h | hmpos
  · rw [← h]
    exact le_max_of_le_right (by positivity)
  set l : ℝ := min (m / M) (P / 2) with hldef
  have hl0 : 0 ≤ l := le_min (by positivity) (by linarith)
  have hkey : m * l - M * l ^ 2 / 2 ≤ eps :=
    tent_area_le hu hbd hint hx0 hl0 (min_le_right _ _)
  rcases le_or_gt (m / M) (P / 2) with hcase | hcase
  · -- the tent fits inside the window: `m²/(2M) ≤ ε`
    rw [hldef, min_eq_left hcase] at hkey
    have hsq : m ^ 2 ≤ 2 * M * eps := by
      have h1 : m * (m / M) - M * (m / M) ^ 2 / 2 = m ^ 2 / (2 * M) := by
        field_simp
        ring
      rw [h1, div_le_iff₀ (by positivity : (0:ℝ) < 2 * M)] at hkey
      linarith
    refine le_max_of_le_left ?_
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hm0] at this
  · -- the tent is truncated by the window: `mP/4 ≤ ε`
    rw [hldef, min_eq_right hcase.le] at hkey
    have hMP : M * (P / 2) < m := by
      rw [lt_div_iff₀ hM] at hcase
      nlinarith
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ hP]
    nlinarith

/-- **From the `L¹` comparison of two curvatures to the uniform one.**  This is
the form in which the bridge is used: the theorem *Curvature-measure matching*
bounds `∫_{J_H}|k₁ − k₂|` while the stability estimates of
`CurvatureStability.lean` consume a uniform bound, and the two derivative
bounds `|kᵢ'| ≤ M/2` supply the missing modulus of continuity. -/
theorem abs_sub_le_of_intervalIntegral_abs_sub_le {k₁ k₂ k₁' k₂' : ℝ → ℝ}
    {c P M eps x0 : ℝ} (hP : 0 < P) (hM : 0 < M)
    (h1 : ∀ x, HasDerivAt k₁ (k₁' x) x) (h2 : ∀ x, HasDerivAt k₂ (k₂' x) x)
    (hb1 : ∀ x, |k₁' x| ≤ M / 2) (hb2 : ∀ x, |k₂' x| ≤ M / 2)
    (hint : (∫ x in c..(c + P), |k₁ x - k₂ x|) ≤ eps)
    (hx0 : x0 ∈ Icc c (c + P)) :
    |k₁ x0 - k₂ x0| ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) := by
  refine abs_le_of_intervalIntegral_abs_le (u := fun x => k₁ x - k₂ x)
    (u' := fun x => k₁' x - k₂' x) hP hM (fun x => (h1 x).sub (h2 x)) (fun x => ?_) hint hx0
  calc |k₁' x - k₂' x| ≤ |k₁' x| + |k₂' x| := abs_sub _ _
    _ ≤ M := by linarith [hb1 x, hb2 x]

end SupFromL1
