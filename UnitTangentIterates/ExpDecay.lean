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
theorem mul_exp_neg_le_exp_neg_one (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) := by
  have h : t ≤ Real.exp (t - 1) := by
    have := Real.add_one_le_exp (t - 1)
    linarith
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  calc t * Real.exp (-t) ≤ Real.exp (t - 1) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        ring_nf

/-- `x e^{-cx} ≤ 1/(c e)` for `c > 0`. -/
theorem mul_exp_neg_le {c x : ℝ} (hc : 0 < c) :
    x * Real.exp (-(c * x)) ≤ 1 / (c * Real.exp 1) := by
  have h := mul_exp_neg_le_exp_neg_one (c * x)
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg]
    simp
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  have hkey : c * (x * Real.exp (-(c * x))) ≤ 1 / Real.exp 1 := by
    rw [← hexp]
    calc c * (x * Real.exp (-(c * x))) = (c * x) * Real.exp (-(c * x)) := by ring
      _ ≤ Real.exp (-1) := h
  rw [le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right hkey hepos.le
  have h3 : (1 / Real.exp 1) * Real.exp 1 = 1 := by field_simp
  nlinarith [h2, h3]

/-- **Absorbing a linear factor into the exponential.**  For `b' < b`,
`x e^{-bx} ≤ (1/((b-b')e)) e^{-b'x}`. -/
theorem linear_exp_decay {b b' x : ℝ} (hb : b' < b) :
    x * Real.exp (-(b * x)) ≤ (1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by
  have hd : 0 < b - b' := by linarith
  have hsplit : Real.exp (-(b * x)) = Real.exp (-((b - b') * x)) * Real.exp (-(b' * x)) := by
    rw [← Real.exp_add]
    ring_nf
  have hmain : x * Real.exp (-((b - b') * x)) ≤ 1 / ((b - b') * Real.exp 1) :=
    mul_exp_neg_le hd
  have hpos : 0 < Real.exp (-(b' * x)) := Real.exp_pos _
  calc x * Real.exp (-(b * x))
      = (x * Real.exp (-((b - b') * x))) * Real.exp (-(b' * x)) := by rw [hsplit]; ring
    _ ≤ (1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) :=
        mul_le_mul_of_nonneg_right hmain hpos.le

/-- **Absorbing an affine factor into the exponential**, in the form used for
the tangent-angle error `(1 + H) e^{-βH}`. -/
theorem one_add_mul_exp_decay {b b' x : ℝ} (hb : b' < b) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(b * x)) ≤
      (1 + 1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by
  have h1 : Real.exp (-(b * x)) ≤ Real.exp (-(b' * x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h2 := linear_exp_decay (x := x) hb
  calc (1 + x) * Real.exp (-(b * x))
      = Real.exp (-(b * x)) + x * Real.exp (-(b * x)) := by ring
    _ ≤ Real.exp (-(b' * x)) + (1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) :=
        add_le_add h1 h2
    _ = (1 + 1 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by ring

end ExpDecay
