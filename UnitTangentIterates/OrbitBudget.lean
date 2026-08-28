import UnitTangentIterates.OrbitCeiling
import UnitTangentIterates.FloorDecay

/-!
# The constructed model sequence meets the backward-orbit budget
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace OrbitBudget

/-- A sequence advancing by at least `d` per step grows at least linearly. -/
theorem le_of_step {H : ℕ → ℝ} {d : ℝ} (hstep : ∀ n, H n + d ≤ H (n + 1)) :
    ∀ n : ℕ, H 0 + n * d ≤ H n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have h := hstep k
      push_cast
      have : H 0 + (k : ℝ) * d + d ≤ H k + d := by linarith
      calc H 0 + ((k : ℝ) + 1) * d = H 0 + (k : ℝ) * d + d := by ring
        _ ≤ H k + d := this
        _ ≤ H (k + 1) := h

/-- **A curvature ceiling `κ ≤ π/H` gives budget at least `H²/π²`.**  The
backward-orbit budget of §84 is `a = 1/κ²`, so a levelwise ceiling decaying like
`1/H` gives a budget growing like `H²`. -/
theorem budget_ge_of_ceiling {kappa H : ℝ} (hH : 0 < H) (hk : 0 < kappa)
    (hkH : kappa ≤ Real.pi / H) : H ^ 2 / Real.pi ^ 2 ≤ 1 / kappa ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : kappa ^ 2 ≤ (Real.pi / H) ^ 2 := by
    have := pow_le_pow_left₀ hk.le hkH 2
    simpa using this
  have hkpos : 0 < kappa ^ 2 := by positivity
  have hrhs : (Real.pi / H) ^ 2 = Real.pi ^ 2 / H ^ 2 := by rw [div_pow]
  rw [hrhs] at hsq
  rw [div_le_div_iff₀ (by positivity) hkpos]
  have hH2 : (0:ℝ) < H ^ 2 := by positivity
  calc H ^ 2 * kappa ^ 2 ≤ H ^ 2 * (Real.pi ^ 2 / H ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hH2.le
    _ = Real.pi ^ 2 := by field_simp
    _ = 1 * Real.pi ^ 2 := (one_mul _).symm

/-- **Linear growth of the levels beats the linear budget demand.**  The demand
of §84's uniformity criterion is `n + A`; a level sequence growing linearly has
budget growing *quadratically*, so the demand is met at every level once the
base level `H₀` is large enough — explicitly, `π² ≤ 2 H₀ d` and `π² A ≤ H₀²`. -/
theorem budget_of_linear_growth {H0 d A : ℝ} (hd : 0 < d) (hH0 : 0 < H0)
    (hA : 1 ≤ A) (ha : Real.pi ^ 2 ≤ 2 * H0 * d) (hb : Real.pi ^ 2 * A ≤ H0 ^ 2)
    (n : ℕ) : (n : ℝ) + A ≤ (H0 + n * d) ^ 2 / Real.pi ^ 2 := by
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  rw [le_div_iff₀ hpi]
  have hexp : (H0 + (n : ℝ) * d) ^ 2
      = H0 ^ 2 + 2 * H0 * d * n + ((n : ℝ) * d) ^ 2 := by ring
  have hsq : (0:ℝ) ≤ ((n : ℝ) * d) ^ 2 := sq_nonneg _
  have hlin : Real.pi ^ 2 * (n : ℝ) ≤ 2 * H0 * d * n :=
    mul_le_mul_of_nonneg_right ha hn
  rw [hexp]
  nlinarith [hlin, hb, hsq]

/-- **The budget criterion for a levelwise-decaying ceiling.**  Combining the
two: a model sequence whose levels advance by at least `d` and whose levelwise
curvature **ceiling** is at most `π / Hₙ` has backward-orbit budget at least
`n + A` at every level.

The ceiling hypothesis `hkH` is an input, and it is *not* the statement proved by
`FloorDecay.levelwise_floor_le`.  That result bounds the levelwise **floor** by
`π / Hₙ`, which follows from the total-turning identity alone; the ceiling does
not, since the turning of a closed curve can be concentrated on a short arc.
For the constructed models the ceiling has to come from the explicit profile
barriers, not from total turning. -/
theorem budget_of_levels {H : ℕ → ℝ} {kappas : ℕ → ℝ} {d A : ℝ}
    (hd : 0 < d) (hH0 : 0 < H 0) (hA : 1 ≤ A)
    (ha : Real.pi ^ 2 ≤ 2 * H 0 * d) (hb : Real.pi ^ 2 * A ≤ H 0 ^ 2)
    (hstep : ∀ n, H n + d ≤ H (n + 1))
    (hkpos : ∀ n, 0 < kappas n) (hkH : ∀ n, kappas n ≤ Real.pi / H n) (n : ℕ) :
    (n : ℝ) + A ≤ 1 / kappas n ^ 2 := by
  have hHn : H 0 + n * d ≤ H n := le_of_step hstep n
  have hHnpos : 0 < H n := by
    have : (0:ℝ) ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg n) hd.le
    linarith
  refine le_trans (budget_of_linear_growth hd hH0 hA ha hb n) ?_
  refine le_trans ?_ (budget_ge_of_ceiling hHnpos (hkpos n) (hkH n))
  have hpi : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hnn : (0:ℝ) ≤ H 0 + n * d := by
    have : (0:ℝ) ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg n) hd.le
    linarith
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hnn hHn 2) hpi.le

/-! ### Validation against the concentric circles

The bicycle rear of a circle of radius `r > 1` is the concentric circle of
radius `√(r²−1)`: the front, the rear and the unit tangent form a right
triangle.  So the ceiling map should send `1/r` to `1/√(r²−1)`, and the budget
`a = 1/κ² = r²` should drop by exactly one.  It does. -/

example {r : ℝ} (hr : 1 < r) : OrbitCeiling.ceilStep (1 / r) = 1 / Real.sqrt (r ^ 2 - 1) := by
  have hr0 : (0:ℝ) < r := by linarith
  have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have ha : (1:ℝ) < r ^ 2 := by nlinarith
  have h := OrbitCeiling.ceilStep_inv_sqrt ha
  rwa [hsq] at h

end OrbitBudget
