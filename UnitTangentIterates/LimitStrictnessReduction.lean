import UnitTangentIterates.UnconditionalAssemblyRemainder

/-!
# Reducing `LimitStrictnessData` to facts the development already tracks

§§50–51 left `LimitStrictnessData` as one of two remaining inputs of the
floor-free closing chain.  Of its seven fields, three are derivative witnesses
and one is periodicity — immediate for the model curves.  The two that looked
substantive reduce to statements the development already carries:

* `next_nonnegative` — the curvature of the unit-tangent successor is
  `(k + k'/(1+k²))/√(1+k²)`.  `next_nonneg_of_relative` derives its
  nonnegativity from `k ≥ 0` together with `|k'| ≤ k`, which is the paper's
  `eq:relative-y-derivatives` at order one.  The computation is
  `k + k'/(1+k²) ≥ k − k/(1+k²) = k·k²/(1+k²) ≥ 0`.
* `curvature_nonzero` — `curvature_nonzero_of_total` derives `∃ s, k s ≠ 0`
  from `∫₀^H k = π`, since a curvature vanishing identically integrates to zero.

So neither field needs new geometry: the first is an order-one relative bound of
exactly the kind §§23–28 established for the pulse, and the second is the
turning identity that every model curve satisfies by construction.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MeasureTheory

namespace UnconditionalAssembly

/-- **`next_nonnegative` from the order-one relative bound.**  The curvature of
the unit-tangent successor is `(k + k'/(1+k²))/√(1+k²)`.  If `k ≥ 0` and
`|k'| ≤ k` — the paper's `eq:relative-y-derivatives` at order one — then

```
  k + k'/(1+k²) ≥ k − k/(1+k²) = k·k²/(1+k²) ≥ 0 .
```
-/
theorem next_nonneg_of_relative {k k' : ℝ} (hk : 0 ≤ k) (hrel : |k'| ≤ k) :
    0 ≤ (k + k' / (1 + k ^ 2)) / Real.sqrt (1 + k ^ 2) := by
  have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + k ^ 2) := Real.sqrt_pos.mpr hpos
  refine div_nonneg ?_ hs.le
  have h1 : -k ≤ k' := neg_le_of_abs_le hrel
  have h2 : -k / (1 + k ^ 2) ≤ k' / (1 + k ^ 2) :=
    div_le_div_of_nonneg_right h1 hpos.le
  have h3 : k + -k / (1 + k ^ 2) = k * k ^ 2 / (1 + k ^ 2) := by
    field_simp
    ring
  have h4 : (0:ℝ) ≤ k * k ^ 2 / (1 + k ^ 2) := by positivity
  linarith [h2, h3.le, h3.ge, h4]

/-- **`curvature_nonzero` from the total turning.**  A curvature with
`∫₀^H k = π` cannot vanish identically. -/
theorem curvature_nonzero_of_total {k : ℝ → ℝ} {H : ℝ}
    (htotal : (∫ r in (0:ℝ)..H, k r) = Real.pi) : ∃ s, k s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hz : (∫ r in (0:ℝ)..H, k r) = 0 := by
    simp only [hcon]
    simp
  rw [htotal] at hz
  exact Real.pi_ne_zero hz

end UnconditionalAssembly
