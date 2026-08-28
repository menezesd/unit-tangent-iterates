import Mathlib
import UnitTangentIterates.PeriodizationDeriv
import UnitTangentIterates.PeriodizationSecondMajorant

/-! # Second differentiation in the period parameter -/

noncomputable section

open Real Set

namespace PeriodizationSecondDerivative

/-- Termwise differentiation of the first period-derivative series. -/
theorem hasDerivAt_firstPeriodDerivativeSeries
    {z1 z2 : ℝ → ℝ} {C alpha H0 H s : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0) (hH : H0 < H)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (fun P => ∑' m : ℤ, (-(m : ℝ)) * z1 (s - (m : ℝ) * P))
      (∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H)) H := by
  let q := Real.exp (-alpha * H0)
  let K := C * Real.exp (alpha * |s|)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hmaj : Summable fun m : ℤ =>
      K * ((m.natAbs : ℝ) ^ 2 * q ^ m.natAbs) :=
    PeriodizationSecondMajorant.summable_natAbs_sq_geometric hq0 hq1
  have hd : ∀ (m : ℤ) (P : ℝ), P ∈ Ioi H0 →
      HasDerivAt (fun R => (-(m : ℝ)) * z1 (s - (m : ℝ) * R))
        ((m : ℝ) ^ 2 * z2 (s - (m : ℝ) * P)) P := by
    intro m P _
    have hin : HasDerivAt (fun R : ℝ => s - (m : ℝ) * R) (-(m : ℝ)) P := by
      convert (hasDerivAt_const P s).sub
        ((hasDerivAt_const P (m : ℝ)).mul (hasDerivAt_id P)) using 1 <;> ring
    convert (hasDerivAt_const P (-(m : ℝ))).mul
      ((hz12 (s - (m : ℝ) * P)).comp P hin) using 1 <;> ring
  have hbound : ∀ (m : ℤ) (P : ℝ), P ∈ Ioi H0 →
      ‖(m : ℝ) ^ 2 * z2 (s - (m : ℝ) * P)‖ ≤
        K * ((m.natAbs : ℝ) ^ 2 * q ^ m.natAbs) := by
    intro m P hP
    simpa [K, q, Real.norm_eq_abs, abs_mul, abs_pow] using
      PeriodizationSecondMajorant.abs_sq_weighted_shift_le
        (w := z2) (C := C) (alpha := alpha) (H0 := H0) (H := P) (s := s)
        halpha hz2b hH0 (le_of_lt hP) m
  have hbase : Summable fun m : ℤ =>
      (-(m : ℝ)) * z1 (s - (m : ℝ) * H) := by
    let K1 := C * Real.exp (alpha * |s|)
    exact Summable.of_norm_bounded
      (PeriodizationDeriv.summable_natAbs_geometric (K := K1) hq0 hq1)
      (fun m => by
        have hb := PeriodizationDeriv.abs_shift_le
          (w := z1) (C := C) (a := alpha) (H₀ := H0) (H := H) (s := s)
          halpha hz1b hH0 hH.le m
        have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
          rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
        rw [Real.norm_eq_abs, abs_mul, hmabs]
        dsimp [K1, q]
        nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m.natAbs)])
  exact hasDerivAt_tsum_of_isPreconnected hmaj isOpen_Ioi isPreconnected_Ioi
    hd hbound (mem_Ioi.mpr hH) hbase (mem_Ioi.mpr hH)

/-- Paper-facing specialization: the second period-derivative series exists
at every positive period. -/
theorem hasDerivAt_firstPeriodDerivativeSeries_of_pos
    {z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (fun P => ∑' m : ℤ, (-(m : ℝ)) * z1 (s - (m : ℝ) * P))
      (∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H)) H := by
  exact hasDerivAt_firstPeriodDerivativeSeries
    halpha (by linarith : 0 < H / 2) (by linarith : H / 2 < H)
    hz12 hz1b hz2b

end PeriodizationSecondDerivative
