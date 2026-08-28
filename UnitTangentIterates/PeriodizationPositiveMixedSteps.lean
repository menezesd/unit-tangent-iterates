import Mathlib
import UnitTangentIterates.PeriodizationMixedTsumSpaceStep
import UnitTangentIterates.PeriodizationMixedPeriodExponential

/-! # Positive-period mixed derivative steps -/

noncomputable section

open Real Set

namespace PeriodizationPositiveMixedSteps

open PeriodizationFiniteDerivativeChain PeriodizationFiniteWeight

/-- Spatial differentiation of an arbitrary fixed mixed series under
exponential derivative bounds. -/
theorem hasDerivAt_tsum_mixedTerm_space_of_exp
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} (r q : ℕ) {alpha s H : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hcur : ∀ x, |zD (r + q) x| ≤ C (r + q) * Real.exp (-alpha * |x|))
    (hnext : ∀ x, |zD ((r + 1) + q) x| ≤
      C ((r + 1) + q) * Real.exp (-alpha * |x|)) :
    HasDerivAt (fun x => ∑' m : ℤ, mixedTerm zD r q x m H)
      (∑' m : ℤ, mixedTerm zD (r + 1) q s m H) s := by
  let K := C ((r + 1) + q) * Real.exp (alpha * (|s| + 1))
  let M : ℤ → ℝ := fun m => K *
    ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H)) ^ m.natAbs)
  have hM : Summable M := by
    have hgeo : Summable fun m : ℤ =>
        ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H)) ^ m.natAbs) := by
      have h := summable_period_weight_majorant (C := (1 : ℝ)) (s := (0 : ℝ))
        (alpha := alpha) (H0 := H) q halpha hH
      simpa using h
    exact hgeo.mul_left K
  have hbound : ∀ (m : ℤ) (x : ℝ), x ∈ Ioo (s - 1) (s + 1) →
      ‖mixedTerm zD (r + 1) q x m H‖ ≤ M m := by
    intro m x hx
    have hxabs : |x| ≤ |s| + 1 := by
      rw [abs_le]
      constructor <;>
        linarith [le_abs_self s, neg_abs_le s, neg_le_abs s, hx.1, hx.2]
    rw [Real.norm_eq_abs, abs_mixedTerm]
    have hb := abs_pow_weighted_shift_le (s := x) q halpha hnext hH le_rfl m
    have hC : 0 ≤ C ((r + 1) + q) := by
      have := hnext 0
      simp at this
      exact le_trans (abs_nonneg _) this
    dsimp [M, K]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hxabs halpha.le)) hC)
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) q) (pow_nonneg (Real.exp_pos _).le _)))
  have hbase : Summable fun m : ℤ => mixedTerm zD r q s m H := by
    let M0 : ℤ → ℝ := fun m => (C (r + q) * Real.exp (alpha * |s|)) *
      ((m.natAbs : ℝ) ^ q * (Real.exp (-alpha * H)) ^ m.natAbs)
    have hM0 : Summable M0 := summable_period_weight_majorant q halpha hH
    refine Summable.of_norm_bounded hM0 ?_
    intro m
    rw [Real.norm_eq_abs, abs_mixedTerm]
    exact abs_pow_weighted_shift_le q halpha hcur hH le_rfl m
  exact PeriodizationMixedTsumSpaceStep.hasDerivAt_tsum_mixedTerm_space
    hz r q s H 1 one_pos hM hbound hbase

/-- Sound all-order certificate, restricted to positive periods. -/
structure PositiveMixedTsumDerivativeSteps (zD : ℕ → ℝ → ℝ) : Prop where
  periodStep : ∀ r q s H, 0 < H → HasDerivAt
    (fun P => ∑' m : ℤ, mixedTerm zD r q s m P)
    (∑' m : ℤ, mixedTerm zD r (q + 1) s m H) H
  spaceStep : ∀ r q s H, 0 < H → HasDerivAt
    (fun x => ∑' m : ℤ, mixedTerm zD r q x m H)
    (∑' m : ℤ, mixedTerm zD (r + 1) q s m H) s

/-- All-order exponential bounds instantiate both recursion directions. -/
theorem exists_positiveMixedTsumDerivativeSteps
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD) {C : ℕ → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hb : ∀ n x, |zD n x| ≤ C n * Real.exp (-alpha * |x|)) :
    PositiveMixedTsumDerivativeSteps zD := by
  refine ⟨?_, ?_⟩
  · intro r q s H hH
    exact PeriodizationMixedPeriodExponential.hasDerivAt_tsum_mixedTerm_period_of_exp
      hz r q halpha hH (hb (r + q)) (hb (r + (q + 1)))
  · intro r q s H hH
    exact hasDerivAt_tsum_mixedTerm_space_of_exp hz r q halpha hH
      (hb (r + q)) (hb ((r + 1) + q))

end PeriodizationPositiveMixedSteps
