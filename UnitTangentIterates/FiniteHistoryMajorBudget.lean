import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.FiniteDiagonalSegmentMajor

/-! # Abstract scalar budgets for finite transition histories -/

noncomputable section

open scoped BigOperators

namespace FiniteHistoryMajorBudget

/-- The scalar interface actually consumed by a finite transition history.
Unlike the configured gauge output, its major is data rather than a
definitionally shifted infinite diagonal. -/
structure MajorBudget (Etotal : ℝ) where
  major : ℕ → ℝ
  nonnegative : ∀ j, 0 ≤ major j
  summable : Summable major
  half : ∀ j, major j ≤ 1 / 2
  tsum_le : (∑' j, major j) ≤ Etotal

namespace MajorBudget

/-- Every legacy configured output supplies the abstract history interface. -/
def ofOutput
    {MA NA Etotal Dtarget : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      J Etotal Dtarget) : MajorBudget Etotal where
  major := O.major
  nonnegative := O.major_nonnegative'
  summable := O.major_summable'
  half := O.major_half'
  tsum_le := O.major_tsum_le'

/-- A fixed-diagonal depth-`k` history, from the exact two scalar closing
inequalities it needs. -/
def ofSegment {Etotal eps : ℝ} (k : ℕ)
    (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (k + 1 : ℕ) * eps ≤ Etotal) : MajorBudget Etotal where
  major := FiniteDiagonalSegmentMajor.segmentMajor eps k
  nonnegative := FiniteDiagonalSegmentMajor.segmentMajor_nonnegative heps k
  summable := FiniteDiagonalSegmentMajor.segmentMajor_summable eps k
  half := by
    intro j
    simp only [FiniteDiagonalSegmentMajor.segmentMajor]
    split
    · exact hhalf
    · norm_num
  tsum_le := by
    rw [FiniteDiagonalSegmentMajor.tsum_segmentMajor]
    exact htotal

@[simp] theorem ofSegment_major_of_le
    {Etotal eps : ℝ} {k j : ℕ}
    (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (k + 1 : ℕ) * eps ≤ Etotal) (hj : j ≤ k) :
    (ofSegment k heps hhalf htotal).major j = eps :=
  FiniteDiagonalSegmentMajor.segmentMajor_eq hj

end MajorBudget

end FiniteHistoryMajorBudget
