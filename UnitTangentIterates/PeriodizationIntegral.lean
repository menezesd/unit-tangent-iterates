module

public import UnitTangentIterates.PeriodizationEstimates

/-!
# The mass of a periodization

For a continuous pulse with exponential decay, `∫₀ᴴ Y_H = ∫_ℝ y`.  In the paper this is the
identity `∫₀ᴴ Y_H = ∫_ℝ y = π` used in Proposition 4.3 (and in Theorem 5.1).
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory intervalIntegral

/-- `t ↦ e^{-a|t|}` is integrable for `a > 0`. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => exp (-(a * |t|))) := by
  set c : ℝ := min 1 (a ^ 2 / 2) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  refine (integrable_inv_one_add_sq.const_mul c⁻¹).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have h1 : 1 + a * |t| + (a * |t|) ^ 2 / 2 ≤ exp (a * |t|) := by
    have := Real.quadratic_le_exp_of_nonneg (x := a * |t|) (by positivity)
    linarith
  have h2 : c * (1 + t ^ 2) ≤ exp (a * |t|) := by
    have hc1 : c ≤ 1 := min_le_left _ _
    have hc2 : c ≤ a ^ 2 / 2 := min_le_right _ _
    have : (a * |t|) ^ 2 = a ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg t, abs_nonneg t, mul_nonneg ha.le (abs_nonneg t)]
  rw [Real.exp_neg, ← mul_inv]
  exact inv_anti₀ (by positivity) h2

variable {y : ℝ → ℝ} {A a : ℝ}

/-- A continuous pulse with exponential decay is integrable. -/
theorem integrable_of_exp_bound (hyc : Continuous y) (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|)))
    (ha : 0 < a) : Integrable y :=
  ((integrable_exp_neg_mul_abs ha).const_mul A).mono' hyc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hyA t)

/-- **Mass of the periodization.**  `∫₀ᴴ Y_H = ∫_ℝ y`. -/
theorem integral_periodize (hyc : Continuous y) (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) :
    ∫ s in (0 : ℝ)..H, periodize y H s = ∫ t, y t := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA 0)) (exp_pos _)
  have hr1 : exp (-(a * H)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  obtain ⟨hgs, -⟩ := summable_geom_natAbs (exp_pos _).le hr1
  -- step 1: exchange sum and integral
  have h1 : HasSum (fun m : ℤ => ∫ s in (0 : ℝ)..H, y (s - m * H))
      (∫ s in (0 : ℝ)..H, periodize y H s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => A * exp (a * H) * exp (-(a * H)) ^ m.natAbs)
      (fun m => (hyc.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun s hs => ?_)
      (Filter.Eventually.of_forall fun s _ => hgs.mul_left _)
      _root_.intervalIntegrable_const
      (Filter.Eventually.of_forall fun s _ => (summable_periodize_abs hyA ha hH s).hasSum)
    rw [Set.uIoc_of_le hH.le] at hs
    rw [Real.norm_eq_abs]
    refine (pulse_shift_le (y := fun t => |y t|) hyA hA ha hH s m).trans ?_
    have : |s| ≤ H := by rw [abs_of_pos hs.1]; exact hs.2
    have h' : exp (a * |s|) ≤ exp (a * H) := Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h' hA) (by positivity)
  -- step 2: unfold the integral over the line
  have h2 : HasSum (fun m : ℤ => ∫ s in (0 : ℝ)..H, y (s - m * H)) (∫ t, y t) := by
    have hint := integrable_of_exp_bound hyc hyA ha
    have hg : Integrable (fun x => y (H * x)) := hint.comp_mul_left' hH.ne'
    have h3 := hg.hasSum_intervalIntegral 0
    have h4 : ∀ n : ℤ, ∫ x in (0 : ℝ) + n..(0 : ℝ) + n + 1, y (H * x) =
        H⁻¹ * ∫ t in (n * H)..(n * H + H), y t := fun n => by
      rw [intervalIntegral.integral_comp_mul_left (fun t => y t) hH.ne', smul_eq_mul]
      congr 2 <;> ring
    have h5 : ∫ x, y (H * x) = H⁻¹ * ∫ t, y t := by
      rw [Measure.integral_comp_mul_left (fun t => y t) H, smul_eq_mul, abs_inv,
        abs_of_pos hH]
    simp_rw [h4, h5] at h3
    have h6 := h3.mul_left H
    simp_rw [← mul_assoc, mul_inv_cancel₀ hH.ne', one_mul] at h6
    have h7 := (Equiv.neg ℤ).hasSum_iff.2 h6
    refine h7.congr_fun fun m => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
    rw [intervalIntegral.integral_comp_sub_right (fun t => y t)]
    congr 1 <;> ring
  exact h1.unique h2

end Ovals

end
