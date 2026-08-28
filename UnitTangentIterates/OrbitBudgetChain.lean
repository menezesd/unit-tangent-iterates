import UnitTangentIterates.OrbitBudgetSharp

/-!
# The budget grows automatically along the level sequence
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace OrbitCeiling

/-- **One rear step costs exactly one unit of budget** — the identity behind
`ceilStep_inv_sqrt`, stated directly on the budget `1/κ²`. -/
theorem budget_ceilStep {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / ceilStep x ^ 2 = 1 / x ^ 2 - 1 := by
  have hx2 : (0:ℝ) < 1 - x ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx2
  have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx2.le
  have hxne : x ^ 2 ≠ 0 := by positivity
  rw [ceilStep, div_pow, hsq, one_div_div]
  field_simp

/-- **The budget increases by exactly one per level.**

The capstone
`InteriorConfiguredModelSequence.exists_configuredModelSequence_of_interior_barrier`
returns `rearPeriod … (Hs (n+1)) = Hs n`: the level-`n` model is the *rear* of
the level-`(n+1)` model.  By `budget_ceilStep` that means the budgets satisfy
`a (n+1) = a n + 1`, so along the level sequence

    1 / κ_m ² = 1 / κ_0 ² + m.

The backward-orbit demand of `OrbitCeiling.ceiling_lt_of_steps` — that the
level-`m` model admit `m` backward steps — is therefore met *by the structure of
the sequence itself*, with `1/κ_0² ` to spare.  No levelwise tuning of `ε` is
required for this. -/
theorem budget_chain {kap : ℕ → ℝ} (hpos : ∀ n, 0 < kap n) (hlt : ∀ n, kap n < 1)
    (hchain : ∀ n, kap n = ceilStep (kap (n + 1))) :
    ∀ m : ℕ, 1 / kap m ^ 2 = 1 / kap 0 ^ 2 + m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      have hstep : 1 / kap k ^ 2 = 1 / kap (k + 1) ^ 2 - 1 := by
        rw [hchain k]
        exact budget_ceilStep (hpos (k + 1)) (hlt (k + 1))
      push_cast
      linarith [ih, hstep]

/-- Hence the ceilings decay like `1/√m` along the level sequence, automatically. -/
theorem ceiling_decay_chain {kap : ℕ → ℝ} (hpos : ∀ n, 0 < kap n)
    (hlt : ∀ n, kap n < 1) (hchain : ∀ n, kap n = ceilStep (kap (n + 1))) (m : ℕ) :
    kap m ≤ 1 / Real.sqrt (m : ℝ) ∨ m = 0 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · exact Or.inr h
  refine Or.inl ?_
  have hb := budget_chain hpos hlt hchain m
  have hm : (0:ℝ) < m := by exact_mod_cast h
  have hk2 : (0:ℝ) < kap m ^ 2 := pow_pos (hpos m) 2
  have hk0 : (0:ℝ) < kap 0 ^ 2 := pow_pos (hpos 0) 2
  have hge : (m : ℝ) ≤ 1 / kap m ^ 2 := by
    have h0 : (0:ℝ) < 1 / kap 0 ^ 2 := one_div_pos.mpr hk0
    linarith
  rw [le_div_iff₀ hk2] at hge          -- `m * kap m ^ 2 ≤ 1`
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  rw [le_div_iff₀ hs]
  have hprod : (kap m * Real.sqrt (m : ℝ)) ^ 2 ≤ 1 := by
    rw [mul_pow, hs2]; linarith
  have hpp : 0 < kap m * Real.sqrt (m : ℝ) := mul_pos (hpos m) hs
  nlinarith [hprod, hpp]

end OrbitCeiling
