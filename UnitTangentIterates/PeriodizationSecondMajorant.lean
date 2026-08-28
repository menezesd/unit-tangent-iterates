import Mathlib
import UnitTangentIterates.PeriodizationDeriv

/-!
# Quadratically weighted periodization majorants

The second derivative in the period parameter introduces the weight `m^2`.
This file supplies the bilateral geometric summability and the exponential
translate majorant needed for the next step of TeX Lemma `lem:periodization`.
-/

noncomputable section

open Real

namespace PeriodizationSecondMajorant

/-- The two-sided quadratically weighted geometric series converges. -/
theorem summable_natAbs_sq_geometric {K q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => K * ((m.natAbs : ℝ) ^ 2 * q ^ m.natAbs)) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hgeo.mul_left K
  · have hshape :
        (fun n : ℕ => K * (((-((n : ℤ) + 1)).natAbs : ℝ) ^ 2 *
          q ^ (-((n : ℤ) + 1)).natAbs)) =
        fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1)) := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [hn]
    rw [hshape]
    have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1)) := by
      simpa using (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) 1).2 hgeo
    exact hs.mul_left K

/-- Exponential decay gives the quadratically weighted majorant used for the
second period derivative, uniformly for all periods above `H0`. -/
theorem abs_sq_weighted_shift_le
    {w : ℝ → ℝ} {C alpha H0 H s : ℝ}
    (halpha : 0 < alpha)
    (hw : ∀ x, |w x| ≤ C * Real.exp (-alpha * |x|))
    (hH0 : 0 < H0) (hH : H0 ≤ H) (m : ℤ) :
    |(m : ℝ)| ^ 2 * |w (s - (m : ℝ) * H)| ≤
      (C * Real.exp (alpha * |s|)) *
        ((m.natAbs : ℝ) ^ 2 * (Real.exp (-alpha * H0)) ^ m.natAbs) := by
  have hb := PeriodizationDeriv.abs_shift_le
    (w := w) (C := C) (a := alpha) (H₀ := H0) (H := H) (s := s)
    halpha hw hH0 hH m
  have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  rw [hmabs]
  convert mul_le_mul_of_nonneg_left hb (sq_nonneg (m.natAbs : ℝ)) using 1 <;>
    ring

/-- Consequently the second-period-derivative majorant is summable. -/
theorem summable_second_period_majorant
    {C alpha H0 s : ℝ} (halpha : 0 < alpha) (hH0 : 0 < H0) :
    Summable (fun m : ℤ =>
      (C * Real.exp (alpha * |s|)) *
        ((m.natAbs : ℝ) ^ 2 * (Real.exp (-alpha * H0)) ^ m.natAbs)) := by
  apply summable_natAbs_sq_geometric
  · exact (Real.exp_pos _).le
  · exact Real.exp_lt_one_iff.mpr (by nlinarith)

end PeriodizationSecondMajorant
