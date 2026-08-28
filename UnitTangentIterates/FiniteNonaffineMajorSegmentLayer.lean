import UnitTangentIterates.FiniteNonaffineMajorLayer

/-! # Fixed-segment specialization of finite-major diagonal layers -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteNonaffineMajorSegmentLayer

open ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  FiniteHistoryMajorBudget

variable {Etotal eps : ℝ} {s k : ℕ} {S : ℕ → Node}

/-- Every row in one fixed diagonal history uses the very same finite budget.
The index accepted by this function is deliberately ignored: it lets the
generic diagonal layer API retain its existing `budget (n+k)` shape while
making predecessor and successor budgets definitionally equal. -/
def segmentBudget (s : ℕ) (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (s + 1 : ℕ) * eps ≤ Etotal) : ℕ → MajorBudget Etotal :=
  fun _ => MajorBudget.ofSegment s heps hhalf htotal

@[simp] theorem segmentBudget_major_of_le
    (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (s + 1 : ℕ) * eps ≤ Etotal) {j : ℕ} (hj : j ≤ s) :
    (segmentBudget s heps hhalf htotal 0).major j = eps :=
  MajorBudget.ofSegment_major_of_le heps hhalf htotal hj

/-- A reached layer whose complete forward history is charged to one fixed
segment budget. -/
abbrev Layer
    (s : ℕ) (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (s + 1 : ℕ) * eps ≤ Etotal)
    (stateP1 defect : ℕ → ℝ) (k : ℕ) (S : ℕ → Node) :=
  FiniteNonaffineMajorLayer.Layer
    (segmentBudget s heps hhalf htotal) stateP1 defect k S

namespace Layer

/-- Advance a fixed-segment layer.  The successor consumes slot `k+1`, so
the only history-index condition is `k+1 ≤ s`; the analytic estimate itself
is stated directly against the constant segment value `eps`. -/
noncomputable def next
    {stateP1 defect : ℕ → ℝ}
    (heps : 0 ≤ eps) (hhalf : eps ≤ 1 / 2)
    (htotal : (s + 1 : ℕ) * eps ≤ Etotal)
    (L : Layer s heps hhalf htotal stateP1 defect k S)
    (G : Step S k)
    (hE : Etotal ≤ 1 / 8) (hslot : k + 1 ≤ s)
    (hcur : ∀ n, (G.analytic n).eps ≤ eps)
    (hupper : ∀ n,
      (G.analytic n).slice.periodUpper ≤ stateP1 (n + (k + 1))) :
    Layer s heps hhalf htotal stateP1 defect (k + 1) G.next := by
  apply FiniteNonaffineMajorLayer.Layer.next
    (segmentBudget s heps hhalf htotal) stateP1 defect L G hE
  · intro n
    change (G.analytic n).eps ≤
      (MajorBudget.ofSegment s heps hhalf htotal).major (k + 1)
    rw [MajorBudget.ofSegment_major_of_le heps hhalf htotal hslot]
    exact hcur n
  · exact hupper

end Layer

end FiniteNonaffineMajorSegmentLayer
