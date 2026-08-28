import Mathlib
import UnitTangentIterates.HairpinRelativeDerivatives

/-!
# A uniform barrier bound for the steering pulse

The paper's hairpin profile satisfies a lower barrier `f ≥ m > 0` on `(0, π)`.
Since `G = sin t / f t` and the steering pulse is `y = G/√(1+G²)`, the barrier
forces `G ≤ 1/m` and hence a bound on the pulse that is **strictly below one**,
uniformly in `t`:

```
  y(t) ≤ 1/√(1+m²) < 1.
```

This is what the configured-model development needs to supply its hypothesis
`sup y ≤ b` with `b < 1`: the bound is not an extra assumption but a
consequence of the barrier the paper already establishes.
-/

noncomputable section

open Set Real HairpinRelative

namespace HairpinRelative

theorem pulseField_le_of_barrier {f : ℝ → ℝ} {m t : ℝ} (hm : 0 < m)
    (hlow : m ≤ f t) (ht : t ∈ Ioo (0:ℝ) π) :
    pulseField f t ≤ 1 / Real.sqrt (1 + m ^ 2) := by
  have hft : 0 < f t := lt_of_lt_of_le hm hlow
  have hG0 : 0 ≤ curvField f t :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2.le) hft.le
  have hGm : curvField f t * m ≤ 1 := by
    rw [curvField, div_mul_eq_mul_div, div_le_one hft]
    nlinarith [Real.sin_le_one t, hlow, hm]
  have hsm : (0:ℝ) < Real.sqrt (1 + m ^ 2) := by positivity
  have hsG : (0:ℝ) < Real.sqrt (1 + curvField f t ^ 2) := sqrt_one_add_sq_pos _
  have hsm2 : Real.sqrt (1 + m ^ 2) ^ 2 = 1 + m ^ 2 :=
    Real.sq_sqrt (by positivity)
  have key : curvField f t * Real.sqrt (1 + m ^ 2)
      ≤ Real.sqrt (1 + curvField f t ^ 2) := by
    refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
    have : (curvField f t * Real.sqrt (1 + m ^ 2)) ^ 2
        = curvField f t ^ 2 * (1 + m ^ 2) := by
      rw [mul_pow, hsm2]
    rw [this]
    have hGmnn : 0 ≤ curvField f t * m := mul_nonneg hG0 hm.le
    have hprod : (curvField f t * m) * (curvField f t * m) ≤ 1 * 1 :=
      mul_le_mul hGm hGm hGmnn zero_le_one
    nlinarith [hprod]
  rw [pulseField, div_le_div_iff₀ hsG hsm]
  linarith [key]

/-- The barrier bound is strictly below one. -/
theorem one_div_sqrt_one_add_sq_lt_one {m : ℝ} (hm : 0 < m) :
    1 / Real.sqrt (1 + m ^ 2) < 1 := by
  have h1 : (1:ℝ) < Real.sqrt (1 + m ^ 2) := by
    have : Real.sqrt 1 < Real.sqrt (1 + m ^ 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      nlinarith
    simpa using this
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

end HairpinRelative
