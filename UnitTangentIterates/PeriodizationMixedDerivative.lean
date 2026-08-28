import Mathlib
import UnitTangentIterates.PeriodizationDeriv

/-! # Mixed spatial/period derivative of a periodization -/

noncomputable section

open Real Set

namespace PeriodizationMixedDerivative

/-- Differentiating the first period-derivative series in the spatial
variable gives `sum_m -m z''(s-mH)`. -/
theorem hasDerivAt_space_firstPeriodDerivativeSeries
    {z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (fun x => ∑' m : ℤ, (-(m : ℝ)) * z1 (x - (m : ℝ) * H))
      (∑' m : ℤ, (-(m : ℝ)) * z2 (s - (m : ℝ) * H)) s := by
  let q := Real.exp (-alpha * H)
  let K := C * Real.exp (alpha * (|s| + 1))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    change Real.exp (-alpha * H) < 1
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hmaj : Summable fun m : ℤ =>
      K * ((m.natAbs : ℝ) * q ^ m.natAbs) :=
    PeriodizationDeriv.summable_natAbs_geometric hq0 hq1
  let U : Set ℝ := Ioo (s - 1) (s + 1)
  have hsU : s ∈ U := by constructor <;> dsimp [U] <;> linarith
  have hd : ∀ (m : ℤ) (x : ℝ), x ∈ U →
      HasDerivAt (fun r => (-(m : ℝ)) * z1 (r - (m : ℝ) * H))
        ((-(m : ℝ)) * z2 (x - (m : ℝ) * H)) x := by
    intro m x _
    convert (hasDerivAt_const x (-(m : ℝ))).mul
      ((hz12 (x - (m : ℝ) * H)).comp x
        ((hasDerivAt_id x).sub_const ((m : ℝ) * H))) using 1 <;> ring
  have hb : ∀ (m : ℤ) (x : ℝ), x ∈ U →
      ‖(-(m : ℝ)) * z2 (x - (m : ℝ) * H)‖ ≤
        K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    intro m x hx
    have hxabs : |x| ≤ |s| + 1 := by
      rcases hx with ⟨hx1, hx2⟩
      exact abs_le.2 ⟨by linarith [neg_le_abs s], by linarith [le_abs_self s]⟩
    have ht := PeriodizationDeriv.abs_shift_le
      (w := z2) (C := C) (a := alpha) (H₀ := H) (H := H) (s := x)
      halpha hz2b hH le_rfl m
    have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
      rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
    rw [Real.norm_eq_abs, abs_mul, hmabs]
    dsimp [K, q]
    have he : C * Real.exp (alpha * |x|) ≤ C * Real.exp (alpha * (|s| + 1)) := by
      have hC := PeriodizationDeriv.const_nonneg hz2b
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hxabs halpha.le)) hC
    nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m.natAbs),
      mul_le_mul_of_nonneg_right he (pow_nonneg hq0 m.natAbs)]
  have hbase : Summable fun m : ℤ =>
      (-(m : ℝ)) * z1 (s - (m : ℝ) * H) := by
    have hb1 : ∀ (m : ℤ),
        ‖(-(m : ℝ)) * z1 (s - (m : ℝ) * H)‖ ≤
          K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
      intro m
      have ht := PeriodizationDeriv.abs_shift_le
        (w := z1) (C := C) (a := alpha) (H₀ := H) (H := H) (s := s)
        halpha hz1b hH le_rfl m
      have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
        rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]
        norm_num
      rw [Real.norm_eq_abs, abs_mul, hmabs]
      dsimp [K, q]
      have he : C * Real.exp (alpha * |s|) ≤
          C * Real.exp (alpha * (|s| + 1)) := by
        have hC := PeriodizationDeriv.const_nonneg hz1b
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m.natAbs),
        mul_le_mul_of_nonneg_right he
          (pow_nonneg (Real.exp_pos (-alpha * H)).le m.natAbs)]
    exact Summable.of_norm_bounded hmaj hb1
  exact hasDerivAt_tsum_of_isPreconnected hmaj isOpen_Ioo isPreconnected_Ioo
    hd hb hsU hbase hsU

end PeriodizationMixedDerivative
