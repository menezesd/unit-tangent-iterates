import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

/-!
# Row-tail transport for finite correlated columns

Dropping the first `N` paper rows reindexes every row-dependent datum while
leaving the recursion depth unchanged.  No configured scalar object is
rebuilt.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

def rowTail {alpha : Sort _} (N : ℕ) (f : ℕ → alpha) : ℕ → alpha :=
  fun n ↦ f (N + n)

def errorRowTail (N : ℕ) (e : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n k ↦ e (N + n) k

/-- Reindex a column step in the row direction. -/
def columnStepRowTail
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (S : TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep
      Q current e k P0 P1 khat G1 Cg C c dlt) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep
      (rowTail N Q) (rowTail N current) (errorRowTail N e) k
      (rowTail N P0) (rowTail N P1) (rowTail N khat)
      (rowTail N G1) (rowTail N Cg) (rowTail N C) c dlt where
  next := rowTail N S.next
  richStage := fun n ↦ by
    simpa [rowTail, errorRowTail, Nat.add_assoc] using S.richStage (N + n)

/-- Reindex a finite correlated column without changing its depth. -/
def FiniteColumn.rowTail
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) :
    FiniteColumn (rowTail N Q) (rowTail N current) (errorRowTail N e) k
      (rowTail N P0) (rowTail N P1) (rowTail N khat)
      (rowTail N G1) (rowTail N Cg) (rowTail N C) c dlt
      (rowTail N kh) (rowTail N Qmax) where
  step := columnStepRowTail S.step
  source := fun n ↦ by
    simpa [columnStepRowTail,
      FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail,
      Nat.add_assoc] using S.source (N + n)
  slice := fun n ↦ by
    simpa [columnStepRowTail,
      FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail,
      Nat.add_assoc] using S.slice (N + n)
  periodUpper_le := fun n ↦ by
    simpa [FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail]
      using S.periodUpper_le (N + n)

/-- `state` commutes with row-tail reindexing. -/
theorem FiniteColumn.rowTail_state
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) :
    (S.rowTail (N := N)).state n = S.state (N + n) := by
  rfl

/-- Reindex all analytic readiness data. -/
def ReadyColumn.rowTail
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) : ReadyColumn (S.rowTail (N := N)) where
  ready := fun n ↦ by
    simpa [FiniteColumn.rowTail_state] using H.ready (N + n)
  initial_range_current := fun n ↦ by
    simpa [FiniteColumn.rowTail, columnStepRowTail,
      FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail] using
      H.initial_range_current (N + n)

/-- The selected presented row commutes with reindexing. -/
theorem ReadyColumn.rowTail_row
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) :
    (H.rowTail (N := N)).row n = H.row (N + n) := by
  rfl

/-- Reindex row geometry and independent cost bounds. -/
def RowBounds.rowTail
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} (B : RowBounds H) : RowBounds (H.rowTail (N := N)) where
  geometry := fun n ↦ by
    simpa [ReadyColumn.rowTail_row,
      FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail]
      using B.geometry (N + n)
  cost_le := fun n ↦ by
    simpa [ReadyColumn.rowTail_row, errorRowTail] using B.cost_le (N + n)

/-- Reindex the retained concrete automatic successor witnesses. -/
def SuccessorBundles.rowTail
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : SuccessorBundles H B) :
    SuccessorBundles (H.rowTail (N := N)) (B.rowTail (N := N)) where
  bundle := fun n ↦ by
    simpa [ReadyColumn.rowTail_row,
      FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail,
      Nat.add_assoc] using X.bundle (N + n)
  periodUpper_le := fun n ↦ by
    simpa [FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.rowTail,
      Nat.add_assoc] using X.periodUpper_le (N + n)

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
