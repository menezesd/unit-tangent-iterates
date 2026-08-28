import UnitTangentIterates.ConfiguredStableRowDefectProvider

/-!
# Diagonally varying stable configured defects

The paper-stable transition may carry a row-dependent polynomial conversion
factor, but never a depth-amplified factor.  This module records precisely that
shape and isolates the one analytic fact needed from a concrete coefficient:
summability along each diagonal.
-/

noncomputable section

open PathMetric

namespace ConfiguredDiagonalStableRowDefectProvider

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

def error (D : ConstructedConfiguredSequenceWeighted.Data)
    (B : ℕ → ℝ) (n k : ℕ) : ℝ :=
  B (n + k) * rowDefect D (n + k)

/-- The exact analytic certificate for a diagonally varying conversion.  It
contains no recursive amplification: the coefficient is evaluated only at
the diagonal index `n+k`. -/
structure Certificate (D : ConstructedConfiguredSequenceWeighted.Data)
    (B : ℕ → ℝ) : Prop where
  coefficient_nonnegative : ∀ m, 0 ≤ B m
  summable_diagonal : ∀ n, Summable (error D B n)

def provider (D : ConstructedConfiguredSequenceWeighted.Data) {B : ℕ → ℝ}
    (hB : Certificate D B) : RowDefectProvider (error D B) where
  nonnegative n k := mul_nonneg (hB.coefficient_nonnegative (n + k))
    ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)
  summable := hB.summable_diagonal

theorem prefix_le_tail
    (D : ConstructedConfiguredSequenceWeighted.Data) {B : ℕ → ℝ}
    (hB : Certificate D B) (n k : ℕ) :
    (∑ j ∈ Finset.range k, error D B n j) ≤
      ShadowingTails.tail (error D B n) 0 := by
  simpa [ShadowingTails.tail] using
    ((provider D hB).summable n |>.sum_le_tsum (Finset.range k)
      (fun j _ => (provider D hB).nonnegative n j))

/-- A fixed stable conversion is the constant special case of the diagonal
interface. -/
def constantCertificate (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cstable : ℝ} (hCstable : 0 ≤ Cstable) :
    Certificate D (fun _ ↦ Cstable) where
  coefficient_nonnegative _ := hCstable
  summable_diagonal n := by
    simpa [error, ConfiguredStableRowDefectProvider.error] using
      ((ConfiguredStableRowDefectProvider.provider D).summable n).mul_left Cstable

end ConfiguredDiagonalStableRowDefectProvider
