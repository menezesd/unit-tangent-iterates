import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
import UnitTangentIterates.RichStageBoundMonotonicity

/-! # Row-tail shifts of finite correlated presented columns -/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion

/-- Enlarge the error allowance at the active depth without changing any
endpoint, source, or analytic slice. -/
def FiniteColumn.monoError
    {Q current : ℕ → Data} {e e' : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (he : ∀ n, e n k ≤ e' n k) :
    FiniteColumn Q current e' k P0 P1 khat G1 Cg C c dlt kh Qmax where
  step := S.step.monoError he
  source := fun n => by
    simpa [TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
      using S.source n
  slice := fun n => by
    simpa [TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
      using S.slice n
  periodUpper_le := S.periodUpper_le

/-- Readiness is unchanged when only the stored cost allowance is enlarged. -/
def ReadyColumn.monoError
    {Q current : ℕ → Data} {e e' : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (he : ∀ n, e n k ≤ e' n k) :
    ReadyColumn (S.monoError he) where
  ready := fun n => by
    simpa [FiniteColumn.state, FiniteColumn.monoError,
      TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
      using H.ready n
  initial_range_current := H.initial_range_current

/-- Drop the first `N` rows of an endpoint-coherent finite column.  This is a
pure reindexing; no path, source, or analytic certificate is changed. -/
def FiniteColumn.shiftRows
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) :
    FiniteColumn
      (fun n => Q (N + n)) (fun n => current (N + n))
      (fun n j => e (N + n) j) k
      (fun n => P0 (N + n)) (fun n => P1 (N + n))
      (fun n => khat (N + n)) (fun n => G1 (N + n))
      (fun n => Cg (N + n)) (fun n => C (N + n)) c dlt
      (fun n => kh (N + n)) (fun n => Qmax (N + n)) where
  step :=
    { next := fun n => S.step.next (N + n)
      richStage := fun n => by
        simpa [Nat.add_assoc] using S.step.richStage (N + n) }
  source := fun n => by
    simpa [Nat.add_assoc] using S.source (N + n)
  slice := fun n => by
    simpa [Nat.add_assoc] using S.slice (N + n)
  periodUpper_le := fun n => S.periodUpper_le (N + n)

@[simp] theorem FiniteColumn.shiftRows_next
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n : ℕ) :
    (S.shiftRows (N := N)).step.next n = S.step.next (N + n) := rfl

@[simp] theorem FiniteColumn.shiftRows_state
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n : ℕ) :
    (S.shiftRows (N := N)).state n = S.state (N + n) := by
  have hindex : N + (n + 1) = N + n + 1 := by omega
  cases hindex
  rfl

/-- Analytic readiness is preserved by the same row-tail reindexing. -/
def ReadyColumn.shiftRows
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k N : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) : ReadyColumn (S.shiftRows (N := N)) where
  ready := fun n => by
    simpa using H.ready (N + n)
  initial_range_current := fun n => by
    simpa using H.initial_range_current (N + n)

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
