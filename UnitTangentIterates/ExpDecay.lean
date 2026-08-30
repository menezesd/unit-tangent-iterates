import Mathlib

/-!
# Absorbing polynomial factors into an exponential

Several estimates of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates* end with a step of the form

```
   ‖Θ_H - Θ_*‖_{L^∞(I_H)} ≤ C H e^{-βH} ≤ C' e^{-β'H} ,
```

that is, a polynomial factor is absorbed by decreasing the exponent slightly
(lemma *Uniform transverse width*, and the analogous steps in the lemma
*Large-separation threshold*).  This file formalizes the elementary
inequalities behind that step, with explicit constants.

Main results:

* `mul_exp_neg_le` : `x e^{-cx} ≤ 1/(c e)`;
* `linear_exp_decay` : `x e^{-bx} ≤ (1/((b-b')e)) e^{-b'x}` for `b' < b`;
* `one_add_mul_exp_decay` : `(1 + x) e^{-bx} ≤ (1 + 1/((b-b')e)) e^{-b'x}` for
  `x ≥ 0`.
-/

noncomputable section

open Real

namespace ExpDecay

/-- The maximum of `t ↦ t e^{-t}` is `1/e`. -/
theorem mul_exp_neg_le_exp_neg_one (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) :=
  Real.mul_exp_neg_le_exp_neg_one t

/-- `x e^{-cx} ≤ 1/(c e)` for `c > 0`. -/
theorem mul_exp_neg_le {c x : ℝ} (hc : 0 < c) :
    x * Real.exp (-(c * x)) ≤ 1 / (c * Real.exp 1) := by
  have h := (div_le_div_iff_of_pos_right hc).2
    (mul_exp_neg_le_exp_neg_one (c * x))
  simpa [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    ne_of_gt hc] using h

/-- **Absorbing a linear factor into the exponential.**  For `b' < b`,
`x e^{-bx} ≤ (1/((b-b')e)) e^{-b'x}`. -/
theorem linear_exp_decay {b b' x : ℝ} (hb : b' < b) :
    x * Real.exp (-(b * x)) ≤ (1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by
  have hsplit : Real.exp (-(b * x)) = Real.exp (-((b - b') * x)) * Real.exp (-(b' * x)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_exp_neg_le (sub_pos.mpr hb))
    (Real.exp_pos _).le

/-- **Absorbing an affine factor into the exponential**, in the form used for
the tangent-angle error `(1 + H) e^{-βH}`. -/
theorem one_add_mul_exp_decay {b b' x : ℝ} (hb : b' < b) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(b * x)) ≤
      (1 + 1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by
  have h1 : Real.exp (-(b * x)) ≤ Real.exp (-(b' * x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [add_mul, one_mul] using add_le_add h1 (linear_exp_decay (x := x) hb)

end ExpDecay
