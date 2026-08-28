import UnitTangentIterates.ConfiguredStableRowDefectProvider

/-!
# Scaled paper-stable configured row defects

This is the scalar consumer of the componentwise stable Jacobi estimate.  A
single conversion constant multiplies the diagonal configured defect; there is
no depth-dependent amplification factor.
-/

noncomputable section

open PathMetric

namespace ConfiguredScaledStableRowDefectProvider

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The error assigned to row `n`, depth `k` after the stable componentwise
Jacobi conversion. -/
def error (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cstable : ℝ) (n k : ℕ) : ℝ :=
  Cstable * rowDefect D (n + k)

theorem error_eq_scale
    (D : ConstructedConfiguredSequenceWeighted.Data) (Cstable : ℝ) :
    error D Cstable = fun n k =>
      Cstable * ConfiguredStableRowDefectProvider.error D n k := by
  rfl

/-- Nonnegative scaling preserves the row-defect provider. -/
def provider (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cstable : ℝ} (hCstable : 0 ≤ Cstable) :
    RowDefectProvider (error D Cstable) where
  nonnegative n k := mul_nonneg hCstable
    ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)
  summable n := by
    simpa [error, ConfiguredStableRowDefectProvider.error] using
      ((ConfiguredStableRowDefectProvider.provider D).summable n).mul_left
        Cstable

/-- Every finite scaled row prefix is controlled by the corresponding scaled
additive tail. -/
theorem prefix_le_tail
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cstable : ℝ} (hCstable : 0 ≤ Cstable) (n k : ℕ) :
    (∑ j ∈ Finset.range k, error D Cstable n j) ≤
      ShadowingTails.tail (error D Cstable n) 0 := by
  simpa [ShadowingTails.tail] using
    ((provider D hCstable).summable n |>.sum_le_tsum (Finset.range k)
      (fun j _ => (provider D hCstable).nonnegative n j))

/-- Pulling a fixed nonnegative scalar through the row tail. -/
theorem tail_eq_scale
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cstable : ℝ) (n : ℕ) :
    ShadowingTails.tail (error D Cstable n) 0 =
      Cstable * ShadowingTails.tail
        (ConfiguredStableRowDefectProvider.error D n) 0 := by
  unfold ShadowingTails.tail error ConfiguredStableRowDefectProvider.error
  rw [tsum_mul_left]

end ConfiguredScaledStableRowDefectProvider
