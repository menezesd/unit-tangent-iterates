import Mathlib
import UnitTangentIterates.MarkingDeviationC2

/-!
# Linearization of the marked `C²` flow defect

The marked acceleration defect contains one quadratic term in the first flow
defect.  On a fixed bounded interval this file absorbs that term into an
explicit linear coefficient.  This is the scalar estimate used when a common
summable `L¹` majorant controls all three marking-flow defects.
-/

noncomputable section

namespace MarkingC2BoundLinearization

open MarkingDeviationC2

/-- An explicit linear coefficient for `markingC2Bound` when its three defect
arguments are fixed multiples of a scalar `x ≤ M`. -/
def linearConstant (a0 a1 a2 M L kb kL : ℝ) : ℝ :=
  max a0 (max (a1 + L * kb * a0)
    (a2 + kb * a1 * (2 * L + a1 * M) + L ^ 2 * (kL + kb ^ 2) * a0))

/-- **Bounded scalar linearization of the marking-flow defect.**

For nonnegative parameters and `x ∈ [0,M]`, the nonlinear marked `C²` defect
is bounded by an explicit fixed multiple of `x`. -/
theorem markingC2Bound_mul_le_linear
    {a0 a1 a2 M L kb kL x : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    markingC2Bound (a0 * x) (a1 * x) (a2 * x) L kb kL
      ≤ linearConstant a0 a1 a2 M L kb kL * x := by
  have hquad :
      kb * (a1 * x) * (2 * L + a1 * x)
        ≤ (kb * a1 * (2 * L + a1 * M)) * x := by
    have key : (0:ℝ) ≤ kb * (a1 * a1) * x * (M - x) :=
      mul_nonneg (mul_nonneg (mul_nonneg hkb (mul_nonneg ha1 ha1)) hx0)
        (sub_nonneg.2 hxM)
    have hid : (kb * a1 * (2 * L + a1 * M)) * x - kb * (a1 * x) * (2 * L + a1 * x)
        = kb * (a1 * a1) * x * (M - x) := by ring
    linarith
  have hpos : a0 * x ≤ linearConstant a0 a1 a2 M L kb kL * x := by
    apply mul_le_mul_of_nonneg_right _ hx0
    exact le_max_left _ _
  have hvel :
      a1 * x + L * kb * (a0 * x)
        ≤ linearConstant a0 a1 a2 M L kb kL * x := by
    rw [show a1 * x + L * kb * (a0 * x) = (a1 + L * kb * a0) * x by ring]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) hx0
  have hacc :
      a2 * x + kb * (a1 * x) * (2 * L + a1 * x) +
          L ^ 2 * (kL + kb ^ 2) * (a0 * x)
        ≤ linearConstant a0 a1 a2 M L kb kL * x := by
    calc
      _ ≤ a2 * x + (kb * a1 * (2 * L + a1 * M)) * x +
          L ^ 2 * (kL + kb ^ 2) * (a0 * x) := by linarith
      _ = (a2 + kb * a1 * (2 * L + a1 * M) +
          L ^ 2 * (kL + kb ^ 2) * a0) * x := by ring
      _ ≤ linearConstant a0 a1 a2 M L kb kL * x :=
        mul_le_mul_of_nonneg_right
          (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  unfold markingC2Bound
  exact max_le hpos (max_le hvel hacc)

/-- Pointwise form convenient for summable-majorant sequence constructions. -/
theorem markingC2Bound_mul_le_linear_pointwise
    {d : ℕ → ℝ} {a0 a1 a2 M L kb kL : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL)
    (hd0 : ∀ n, 0 ≤ d n) (hdM : ∀ n, d n ≤ M) (n : ℕ) :
    markingC2Bound (a0 * d n) (a1 * d n) (a2 * d n) L kb kL
      ≤ linearConstant a0 a1 a2 M L kb kL * d n :=
  markingC2Bound_mul_le_linear ha0 ha1 ha2 hM hL hkb hkL (hd0 n) (hdM n)

end MarkingC2BoundLinearization
