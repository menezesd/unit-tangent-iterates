import UnitTangentIterates.ArclengthInverse

/-!
# The curvature ceiling and the perimeter along the backward orbit
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real Finset

namespace OrbitCeiling

/-- **The curvature-ceiling step of the rear map.**  The rear of a curve of
curvature at most `κ` has curvature at most `κ / √(1-κ²)`. -/
def ceilStep (x : ℝ) : ℝ := x / Real.sqrt (1 - x ^ 2)

/-- **In the coordinate `a = 1/κ²` the ceiling step is `a ↦ a - 1`.**  This is
the whole arithmetic of the backward orbit: the ceiling does not merely grow, it
grows by consuming exactly one unit of `1/κ²` per step, so a curve of ceiling
`κ₀` admits at most `1/κ₀²` backward steps before the bound blows up. -/
theorem ceilStep_inv_sqrt {a : ℝ} (ha : 1 < a) :
    ceilStep (1 / Real.sqrt a) = 1 / Real.sqrt (a - 1) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have ha1 : (0:ℝ) < a - 1 := by linarith
  have hsa1 : 0 < Real.sqrt (a - 1) := Real.sqrt_pos.mpr ha1
  have hsq : (1 / Real.sqrt a) ^ 2 = 1 / a := by
    rw [div_pow, one_pow, Real.sq_sqrt ha0.le]
  have hone : 1 - (1 / Real.sqrt a) ^ 2 = (a - 1) / a := by
    rw [hsq]; field_simp
  have hdiv : Real.sqrt ((a - 1) / a) = Real.sqrt (a - 1) / Real.sqrt a :=
    Real.sqrt_div ha1.le a
  rw [ceilStep, hone, hdiv]
  field_simp

/-- **The ceiling after `k` backward steps.**  `κ_k = 1/√(1/κ₀² − k)`, valid
exactly while `k < 1/κ₀²`. -/
theorem ceilStep_iterate {a : ℝ} : ∀ k : ℕ, (k : ℝ) < a →
    ceilStep^[k] (1 / Real.sqrt a) = 1 / Real.sqrt (a - k) := by
  intro k
  induction k generalizing a with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have ha : 1 < a := by push_cast at hk; linarith
      rw [Function.iterate_succ_apply, ceilStep_inv_sqrt ha]
      have hk' : (k : ℝ) < a - 1 := by push_cast at hk; linarith
      rw [ih hk']
      push_cast
      ring_nf

/-- The speed factor of one backward step, at ceiling `1/√a`. -/
theorem speed_factor {a : ℝ} (ha : 1 ≤ a) :
    Real.sqrt (1 - (1 / Real.sqrt a) ^ 2) = Real.sqrt (a - 1) / Real.sqrt a := by
  have ha0 : (0:ℝ) < a := by linarith
  have hsq : (1 / Real.sqrt a) ^ 2 = 1 / a := by
    rw [div_pow, one_pow, Real.sq_sqrt ha0.le]
  have hone : 1 - (1 / Real.sqrt a) ^ 2 = (a - 1) / a := by
    rw [hsq]; field_simp
  rw [hone, Real.sqrt_div (by linarith) a]

/-- **The perimeter factor telescopes.**  Each backward step multiplies the
perimeter by at least `√(1-κ_j²)`, and along the orbit `κ_j = 1/√(a-j)`, so the
product over `k` steps collapses to `√((a-k)/a)` — the losses do not compound
into anything worse than the single ratio of endpoints. -/
theorem prod_speed_factors {a : ℝ} : ∀ k : ℕ, (k : ℝ) ≤ a - 1 →
    ∏ j ∈ Finset.range k, Real.sqrt (1 - (1 / Real.sqrt (a - j)) ^ 2)
      = Real.sqrt (a - k) / Real.sqrt a := by
  intro k
  induction k with
  | zero =>
      intro h
      have ha0 : (0:ℝ) < a := by push_cast at h; linarith
      simp [div_self (Real.sqrt_pos.mpr ha0).ne']
  | succ k ih =>
      intro hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hka : (k : ℝ) ≤ a - 1 := by push_cast at hk; linarith
      rw [Finset.prod_range_succ, ih hka]
      have hone : (1:ℝ) ≤ a - k := by push_cast at hk; linarith
      rw [speed_factor hone]
      have hpa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
      have hpos : 0 < Real.sqrt (a - k) := Real.sqrt_pos.mpr (by linarith)
      have hcast : a - ((k + 1 : ℕ) : ℝ) = a - k - 1 := by push_cast; ring
      rw [hcast]
      field_simp


/-! ### The uniformity criterion

Both orbit constants depend on `k` only through the *remaining budget* `a - k`.
So a family of models whose budgets exceed the number of backward steps taken
from them by a fixed amount `A` yields uniform constants — which is exactly the
form the closing chain's `hmem` needs, and exactly why the models `Q n` have to
grow with `n`. -/

/-- With budget `A` to spare, the ceiling after `k` steps is at most `1/√A`. -/
theorem ceiling_le_of_budget {a A : ℝ} (k : ℕ) (hA : 1 ≤ A) (hk : (k : ℝ) + A ≤ a) :
    ceilStep^[k] (1 / Real.sqrt a) ≤ 1 / Real.sqrt A := by
  have hka : (k : ℝ) < a := by linarith
  rw [ceilStep_iterate k hka]
  have hApos : (0:ℝ) < A := by linarith
  have hle : Real.sqrt A ≤ Real.sqrt (a - (k : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hApos) hle

/-- With budget `A` to spare, the accumulated perimeter factor after `k` steps
is at least `√(A/a)`. -/
theorem speed_prod_ge_of_budget {a A : ℝ} (k : ℕ) (hA : 1 ≤ A) (hk : (k : ℝ) + A ≤ a) :
    Real.sqrt (A / a) ≤
      ∏ j ∈ Finset.range k, Real.sqrt (1 - (1 / Real.sqrt (a - j)) ^ 2) := by
  have hka : (k : ℝ) ≤ a - 1 := by linarith
  have hapos : (0:ℝ) < a := by linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [prod_speed_factors k hka, Real.sqrt_div (by linarith) a]
  have hsa : (0:ℝ) < Real.sqrt a := Real.sqrt_pos.mpr hapos
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hsa.le

end OrbitCeiling
