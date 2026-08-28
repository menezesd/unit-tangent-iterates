import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant

/-! # Tail shifts of configured gauge-majorant outputs -/

noncomputable section

open Filter MeasureTheory

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget.WeightedData

variable {MA NA Etotal Dtarget : ℝ}
  {J : RowJetScalarOutput MA NA}

namespace ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output

/-- Shift an already closed gauge output to a later row.  Its local major at
depth `j` is the original major at `N+j`; no monotonicity is used. -/
def shiftOutput (O : Output J Etotal Dtarget) (N : ℕ) :
    Output J Etotal Dtarget where
  N := O.N + N
  major_nonnegative := by
    intro j
    rw [combinedGaugeMajor_shift]
    have H := O.major_nonnegative' (N + j)
    rw [Output.major, Output.data, combinedGaugeMajor_shift] at H
    simpa [Nat.add_assoc] using H
  major_summable := by
    have H : Summable (fun j ↦ O.major (N + j)) :=
      O.major_summable'.comp_injective (add_right_injective N)
    refine H.congr ?_
    intro j
    simp [Output.major, Output.data, combinedGaugeMajor_shift, Nat.add_assoc]
  major_half := by
    intro j
    rw [combinedGaugeMajor_shift]
    have H := O.major_half' (N + j)
    rw [Output.major, Output.data, combinedGaugeMajor_shift] at H
    simpa [Nat.add_assoc] using H
  major_tsum_le := by
    have Hsum := O.major_summable'.sum_add_tsum_nat_add N
    have Hnonneg : 0 ≤ ∑ i ∈ Finset.range N, O.major i := by
      exact Finset.sum_nonneg fun i _ ↦ O.major_nonnegative' i
    have Htail : (∑' j, O.major (j + N)) ≤ Etotal := by
      linarith [O.major_tsum_le']
    have Heq : (∑' j, combinedGaugeMajor
        (shift (shift J.scalar.E.data J.scalar.large.N) (O.N + N))
          J.scalar.Mend Dtarget j) =
        ∑' j, O.major (j + N) := by
      apply tsum_congr
      intro j
      simp [Output.major, Output.data, combinedGaugeMajor_shift,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [Heq]
    exact Htail

@[simp] theorem shiftOutput_N (O : Output J Etotal Dtarget) (N : ℕ) :
    (O.shiftOutput N).N = O.N + N := rfl

@[simp] theorem shiftOutput_major (O : Output J Etotal Dtarget) (N j : ℕ) :
    (O.shiftOutput N).major j = O.major (N + j) := by
  simp [Output.major, Output.data, combinedGaugeMajor_shift, Nat.add_assoc]

end ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
