import Mathlib
import UnitTangentIterates.PeriodizationDeriv

/-! # Arbitrary finite polynomial weights in bilateral periodizations -/

noncomputable section

open Real

namespace PeriodizationFiniteWeight

/-- For every finite order `q`, the bilateral series
`sum_m |m|^q rho^|m|` converges when `0 <= rho < 1`. -/
theorem summable_natAbs_pow_geometric (q : ℕ) {K rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    Summable (fun m : ℤ => K * ((m.natAbs : ℝ) ^ q * rho ^ m.natAbs)) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ q * rho ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) q
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hrho0])
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hgeo.mul_left K
  · have hshape :
        (fun n : ℕ => K * (((-((n : ℤ) + 1)).natAbs : ℝ) ^ q *
          rho ^ (-((n : ℤ) + 1)).natAbs)) =
        fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) ^ q * rho ^ (n + 1)) := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [hn]
    rw [hshape]
    have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ q * rho ^ (n + 1)) := by
      simpa using (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ q * rho ^ n) 1).2 hgeo
    exact hs.mul_left K

/-- Exponential tails dominate the arbitrary finite translation-index weight
appearing after `q` differentiations in the period. -/
theorem abs_pow_weighted_shift_le
    {w : ℝ → ℝ} {C alpha H0 H s : ℝ} (q : ℕ)
    (halpha : 0 < alpha)
    (hw : ∀ x, |w x| ≤ C * Real.exp (-alpha * |x|))
    (hH0 : 0 < H0) (hH : H0 ≤ H) (m : ℤ) :
    |(m : ℝ)| ^ q * |w (s - (m : ℝ) * H)| ≤
      (C * Real.exp (alpha * |s|)) *
        ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H0)) ^ m.natAbs) := by
  have hb := PeriodizationDeriv.abs_shift_le
    (w := w) (C := C) (a := alpha) (H₀ := H0) (H := H) (s := s)
    halpha hw hH0 hH m
  have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  rw [hmabs]
  convert mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg _) q) using 1 <;>
    ring

/-- The explicit arbitrary-order exponential majorant is summable. -/
theorem summable_period_weight_majorant
    (q : ℕ) {C alpha H0 s : ℝ} (halpha : 0 < alpha) (hH0 : 0 < H0) :
    Summable (fun m : ℤ =>
      (C * Real.exp (alpha * |s|)) *
        ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H0)) ^ m.natAbs)) := by
  apply summable_natAbs_pow_geometric q
  · exact (Real.exp_pos _).le
  · exact Real.exp_lt_one_iff.mpr (by nlinarith)

end PeriodizationFiniteWeight
