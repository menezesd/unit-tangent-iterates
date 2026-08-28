import UnitTangentIterates.LevelwiseProfiles

/-!
# How fast the levels must grow when the constants degrade with the level
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real Filter

namespace LevelGrowth

theorem summable_inv_sq_shift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact ((summable_nat_add_iff 2).mpr h).congr (by intro n; push_cast; ring_nf)

/-- `exp (-(2 log x)) = 1/x²`. -/
theorem exp_neg_two_log {x : ℝ} (hx : 0 < x) :
    Real.exp (-(2 * Real.log x)) = 1 / x ^ 2 := by
  have hlog : (2:ℝ) * Real.log x = Real.log (x ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [hlog, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- **The growth criterion.**  If the level `H(n+1)` grows fast enough to absorb
the degrading decay rate `beta n` — precisely, if `beta n * H (n+1) ≥ 2 log (n+2)`
— then the defect series `∑ exp(−beta n · H (n+1))` converges.

This is what replaces the fixed-constant summability argument once `ε` is chosen
per level.  With `ε_n ≍ 1/√(n+1)` the profile's tail constant `Am_n ≍ 1/ε_n`
grows, so the decay rate degrades like `1/√(n+1)`; the criterion says the levels
need only outgrow that by a logarithm. -/
theorem summable_defect_of_growth {beta H : ℕ → ℝ}
    (hcrit : ∀ n : ℕ, 2 * Real.log ((n : ℝ) + 2) ≤ beta n * H (n + 1)) :
    Summable (fun n : ℕ => Real.exp (-(beta n * H (n + 1)))) := by
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    summable_inv_sq_shift
  have hpos : (0:ℝ) < (n : ℝ) + 2 := by positivity
  rw [← exp_neg_two_log hpos]
  exact Real.exp_le_exp.mpr (by linarith [hcrit n])

/-- **The criterion is met by quadratic levels against a `1/√n` decay rate.**
With `beta n = b₀/√(n+1)` and `H (n+1) = c (n+2)²`, the criterion holds as soon
as `2 ≤ b₀ c` — no largeness beyond that is needed. -/
theorem growth_criterion_of_quadratic {b0 c : ℝ} (hb0 : 0 < b0) (hc : 0 < c)
    (hcb : 2 ≤ b0 * c) (n : ℕ) :
    2 * Real.log ((n : ℝ) + 2)
      ≤ (b0 / Real.sqrt ((n : ℝ) + 1)) * (c * ((n : ℝ) + 2) ^ 2) := by
  have h1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr h1
  have hlog : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := Real.log_le_self h2.le
  -- `√(n+1) ≤ n+2`
  have hsle : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 2 := by
    have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt h1.le
    nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1)]
  -- so `b₀ c (n+2)² / √(n+1) ≥ b₀ c (n+2) ≥ 2 (n+2) ≥ 2 log (n+2)`
  have hstep : b0 * c * ((n : ℝ) + 2) ≤ (b0 / Real.sqrt ((n : ℝ) + 1)) * (c * ((n : ℝ) + 2) ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    nlinarith [mul_pos hb0 hc, hsle, h2, mul_pos (mul_pos hb0 hc) h2]
  have hfin : 2 * ((n : ℝ) + 2) ≤ b0 * c * ((n : ℝ) + 2) := by nlinarith
  linarith


/-- **The two composed.**  Quadratic levels against a `1/√n` decay rate give a
summable defect series.  Stated separately because `H (n+1)` and `(n+2)` differ
by a cast that is not definitional. -/
theorem summable_defect_quadratic {b0 c : ℝ} (hb0 : 0 < b0) (hc : 0 < c)
    (hcb : 2 ≤ b0 * c) :
    Summable (fun n : ℕ =>
      Real.exp (-((b0 / Real.sqrt ((n : ℝ) + 1)) * (c * ((n : ℝ) + 2) ^ 2)))) := by
  have hcrit : ∀ n : ℕ, 2 * Real.log ((n : ℝ) + 2)
      ≤ (b0 / Real.sqrt ((n : ℝ) + 1)) * (c * (((n + 1 : ℕ) : ℝ) + 1) ^ 2) := by
    intro n
    have h := growth_criterion_of_quadratic hb0 hc hcb n
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hcast]
    exact h
  have hsum := summable_defect_of_growth
    (beta := fun n : ℕ => b0 / Real.sqrt ((n : ℝ) + 1))
    (H := fun m : ℕ => c * ((m : ℝ) + 1) ^ 2) hcrit
  refine hsum.congr (fun n => ?_)
  simp only []
  congr 2
  push_cast
  ring

end LevelGrowth
