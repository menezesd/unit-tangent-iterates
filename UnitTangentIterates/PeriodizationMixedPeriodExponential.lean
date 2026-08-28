import Mathlib
import UnitTangentIterates.PeriodizationMixedTsumStep

/-! # Exponential instantiation of one arbitrary period-derivative step -/

noncomputable section

open Real Set

namespace PeriodizationMixedPeriodExponential

open PeriodizationFiniteDerivativeChain PeriodizationFiniteWeight

/-- For fixed finite `r,q`, exponential bounds at derivative orders `r+q`
and `r+q+1` instantiate the period-direction tsum interchange. -/
theorem hasDerivAt_tsum_mixedTerm_period_of_exp
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} (r q : ℕ) {alpha s H : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hcur : ∀ x, |zD (r + q) x| ≤ C (r + q) * Real.exp (-alpha * |x|))
    (hnext : ∀ x, |zD (r + (q + 1)) x| ≤
      C (r + (q + 1)) * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (fun P => ∑' m : ℤ, mixedTerm zD r q s m P)
      (∑' m : ℤ, mixedTerm zD r (q + 1) s m H) H := by
  let H0 := H / 2
  let rho := H / 4
  let M : ℤ → ℝ := fun m =>
    (C (r + (q + 1)) * Real.exp (alpha * |s|)) *
      ((m.natAbs : ℝ) ^ (q + 1) * (Real.exp (-alpha * H0)) ^ m.natAbs)
  have hH0 : 0 < H0 := by dsimp [H0]; linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hM : Summable M := by
    dsimp [M]
    exact summable_period_weight_majorant (q + 1) halpha hH0
  have hbound : ∀ (m : ℤ) (P : ℝ), P ∈ Ioo (H - rho) (H + rho) →
      ‖mixedTerm zD r (q + 1) s m P‖ ≤ M m := by
    intro m P hP
    have hPH0 : H0 ≤ P := by
      have hlow : H - rho < P := hP.1
      have hr : rho = H / 4 := rfl
      have h0 : H0 = H / 2 := rfl
      rw [hr] at hlow
      rw [h0]
      linarith
    rw [Real.norm_eq_abs, abs_mixedTerm]
    dsimp [M]
    exact abs_pow_weighted_shift_le (q + 1) halpha hnext hH0 hPH0 m
  have hbase : Summable fun m : ℤ => mixedTerm zD r q s m H := by
    let M0 : ℤ → ℝ := fun m =>
      (C (r + q) * Real.exp (alpha * |s|)) *
        ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H0)) ^ m.natAbs)
    have hM0 : Summable M0 := by
      dsimp [M0]
      exact summable_period_weight_majorant q halpha hH0
    refine Summable.of_norm_bounded hM0 ?_
    intro m
    rw [Real.norm_eq_abs, abs_mixedTerm]
    dsimp [M0]
    have hH0H : H0 ≤ H := by
      have h0 : H0 = H / 2 := rfl
      rw [h0]; linarith
    exact abs_pow_weighted_shift_le q halpha hcur hH0 hH0H m
  exact PeriodizationMixedTsumStep.hasDerivAt_tsum_mixedTerm_period
    hz r q s H rho hrho hM hbound hbase

end PeriodizationMixedPeriodExponential
