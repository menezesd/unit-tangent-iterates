import Mathlib

/-!
# Global first- and second-order bounds for a function of one variable

Small analytic toolbox used to check the curvature hypotheses of the
path-distance assembly for a concrete family of fronts:

* `exists_bound_of_vanishing_outside` — a continuous function vanishing outside
  a compact interval is globally bounded;
* `abs_sub_le_of_deriv_bound` — a global bound on the derivative is a global
  Lipschitz bound;
* `abs_taylor_quadratic` — a global bound on the second derivative gives the
  first-order Taylor bound `|g a − g b − (a−b) g'(b)| ≤ M (a−b)²`.
-/

noncomputable section

open Set

namespace SecondOrderBounds

/-- A continuous function vanishing outside a compact interval is bounded. -/
theorem exists_bound_of_vanishing_outside {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hzero : ∀ x, x ∉ Icc a b → f x = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hf.norm.continuousOn)
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc a b
  · exact le_trans (by simpa [Real.norm_eq_abs] using hM x hx) (le_max_left _ _)
  · rw [hzero x hx]; simp

/-- A global bound on the derivative is a global Lipschitz bound. -/
theorem abs_sub_le_of_deriv_bound {g g' : ℝ → ℝ} {M : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, |g' x| ≤ M) (a b : ℝ) :
    |g a - g b| ≤ M * |a - b| := by
  have hconv : Convex ℝ (uIcc b a) := convex_uIcc b a
  have hd : ∀ x ∈ uIcc b a, HasDerivWithinAt g (g' x) (uIcc b a) x :=
    fun x _ => (hg x).hasDerivWithinAt
  have hb : ∀ x ∈ uIcc b a, ‖g' x‖ ≤ M := fun x _ => by
    simpa [Real.norm_eq_abs] using hM x
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_uIcc) (right_mem_uIcc)
  simpa [Real.norm_eq_abs] using this

/-- A global bound on the second derivative gives the first-order Taylor
bound. -/
theorem abs_taylor_quadratic {g g' g'' : ℝ → ℝ} {M : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hM : ∀ x, |g'' x| ≤ M) (a b : ℝ) :
    |g a - g b - (a - b) * g' b| ≤ M * (a - b) ^ 2 := by
  set h : ℝ → ℝ := fun x => g x - g b - (x - b) * g' b with hh
  have hderiv : ∀ x, HasDerivAt h (g' x - g' b) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => g x - g b) (g' x) x := (hg x).sub_const _
    have h2 : HasDerivAt (fun x : ℝ => (x - b) * g' b) (1 * g' b) x :=
      ((hasDerivAt_id x).sub_const b).mul_const _
    simpa [hh, one_mul] using h1.sub h2
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM b)
  have hconv : Convex ℝ (uIcc b a) := convex_uIcc b a
  have hbound : ∀ x ∈ uIcc b a, ‖g' x - g' b‖ ≤ M * |a - b| := by
    intro x hx
    have hxb : |x - b| ≤ |a - b| := by
      rcases le_total b a with hba | hba
      · rw [uIcc_of_le hba] at hx
        rw [abs_of_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - b),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
        linarith [hx.2]
      · rw [uIcc_of_ge hba] at hx
        rw [abs_of_nonpos (by linarith [hx.2] : x - b ≤ 0),
          abs_of_nonpos (by linarith : a - b ≤ 0)]
        linarith [hx.1]
    have := abs_sub_le_of_deriv_bound hg' hM x b
    calc ‖g' x - g' b‖ = |g' x - g' b| := Real.norm_eq_abs _
      _ ≤ M * |x - b| := this
      _ ≤ M * |a - b| := by
          exact mul_le_mul_of_nonneg_left hxb hMnn
  have hd : ∀ x ∈ uIcc b a, HasDerivWithinAt h (g' x - g' b) (uIcc b a) x :=
    fun x _ => (hderiv x).hasDerivWithinAt
  have hmain := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
    (left_mem_uIcc) (right_mem_uIcc)
  have hhb : h b = 0 := by simp [hh]
  have hha : h a = g a - g b - (a - b) * g' b := rfl
  have hsq : |a - b| * |a - b| = (a - b) ^ 2 := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (a - b))]; ring
  calc |g a - g b - (a - b) * g' b| = ‖h a - h b‖ := by
        rw [hhb, hha]; simp [Real.norm_eq_abs]
    _ ≤ M * |a - b| * ‖a - b‖ := hmain
    _ = M * (a - b) ^ 2 := by
        rw [Real.norm_eq_abs, mul_assoc, hsq]

end SecondOrderBounds
