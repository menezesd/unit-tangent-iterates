import UnitTangentIterates.OrbitBudget

/-!
# The budget is sharp: how many backward steps a curvature ceiling permits
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace OrbitCeiling

/-- The iterate formula, written directly in the ceiling `κ` rather than in the
budget coordinate `a = 1/κ²`. -/
theorem ceilStep_iterate' {kappa : ℝ} (hk : 0 < kappa) (k : ℕ)
    (hkk : (k : ℝ) < 1 / kappa ^ 2) :
    ceilStep^[k] kappa = 1 / Real.sqrt (1 / kappa ^ 2 - k) := by
  have hk2 : (0:ℝ) < kappa ^ 2 := by positivity
  have hinv : kappa = 1 / Real.sqrt (1 / kappa ^ 2) := by
    rw [one_div (kappa ^ 2), Real.sqrt_inv, one_div, inv_inv, Real.sqrt_sq hk.le]
  conv_lhs => rw [hinv]
  exact ceilStep_iterate k hkk

/-- **The budget is exactly the number of admissible backward steps.**  Every
construction in the development requires the curvature ceiling to stay below
one — `hkap1 : kap < 1` is a hypothesis of `exists_marked_rearOwn`,
`isOval_rearOwn`, `injOn_rearTrack_of_curvature_nonnegative`, and the steering
existence theorem.  After `k` backward steps the ceiling is `1/√(a-k)`, so it
stays below one exactly while `k < a - 1`. -/
theorem ceiling_lt_one_iff {a : ℝ} {k : ℕ} (hk : (k : ℝ) < a) :
    ceilStep^[k] (1 / Real.sqrt a) < 1 ↔ (k : ℝ) < a - 1 := by
  rw [ceilStep_iterate k hk]
  have hpos : (0:ℝ) < a - k := by linarith
  have hsq : 0 < Real.sqrt (a - k) := Real.sqrt_pos.mpr hpos
  rw [div_lt_one hsq]
  constructor
  · intro h
    have h1 : (1:ℝ) < a - k := by
      nlinarith [Real.sq_sqrt hpos.le, Real.sqrt_nonneg (a - (k : ℝ))]
    linarith
  · intro h
    have h1 : (1:ℝ) < a - k := by linarith
    have h2 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) h1
    rwa [Real.sqrt_one] at h2

/-- **The ceiling of a curve admitting `k` backward steps is below `1/√(k+1)`.**

This is the sharp necessary condition on the models.  The pullback the closing
chain uses at level `n` is `B^[k] (Q (n+k))`, so the model at level `m` must
admit `m - n` backward steps for every `n ≤ m`.  Taking `n = 0`: the model at
level `m` must have curvature ceiling below `1/√(m+1)`.

A model sequence with a *fixed* ceiling therefore cannot support the pullback
construction at every level, however large its periods `Hₙ` grow — the periods
are irrelevant to this obstruction, which is entirely about the ceiling. -/
theorem ceiling_lt_of_steps {kappa : ℝ} {k : ℕ} (hk : 0 < kappa)
    (hkk : (k : ℝ) < 1 / kappa ^ 2) (h : ceilStep^[k] kappa < 1) :
    kappa < 1 / Real.sqrt (k + 1) := by
  have hk2 : (0:ℝ) < kappa ^ 2 := by positivity
  have hinv : kappa = 1 / Real.sqrt (1 / kappa ^ 2) := by
    rw [one_div (kappa ^ 2), Real.sqrt_inv, one_div, inv_inv, Real.sqrt_sq hk.le]
  rw [hinv] at h
  have hbudget : (k : ℝ) < 1 / kappa ^ 2 - 1 := (ceiling_lt_one_iff hkk).mp h
  have hkey : (k : ℝ) + 1 < 1 / kappa ^ 2 := by linarith
  have hpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hsq : kappa ^ 2 < 1 / ((k : ℝ) + 1) := by
    rw [lt_div_iff₀ hpos]
    rw [lt_div_iff₀ hk2] at hkey
    linarith
  have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hpos
  rw [lt_div_iff₀ hs]
  have hs2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt hpos.le
  have hprod : (kappa * Real.sqrt ((k : ℝ) + 1)) ^ 2 < 1 := by
    rw [mul_pow, hs2]
    rw [lt_div_iff₀ hpos] at hsq
    linarith
  have hposprod : 0 < kappa * Real.sqrt ((k : ℝ) + 1) := mul_pos hk hs
  nlinarith [hprod, hposprod]

end OrbitCeiling
