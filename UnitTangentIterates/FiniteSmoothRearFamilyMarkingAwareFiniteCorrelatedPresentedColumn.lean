import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricExactPresentedRowConstructor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds

/-!
# Finite correlated presented columns

This module retains the triangular endpoint indexing of `ColumnStep` while
discarding the legacy scalar-period transition certificate.  Analytic rows are
produced by the theorem-driven presented-row constructor.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
open FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
open FiniteSmoothRearFamilyMarkingAwareGeometricExactPresentedRowConstructor
open FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

/-- The endpoint-coherent part of a correlated column, with no transition
certificate and no component bound baked into its definition. -/
structure FiniteColumn
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (kh Qmax : ℕ → ℝ) where
  step : TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep
    Q current e k P0 P1 khat G1 Cg C c dlt
  source : (n : ℕ) →
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      (step.richStage (n + 1)).stage.increment
      (P0 n) (kh n) (khat n) (Qmax n)
  slice : (n : ℕ) → AnalyticSuccessorSliceFacts (source n)
  periodUpper_le : ∀ n, (slice n).periodUpper ≤ P1 n

/-- Project a legacy correlated column to its sound endpoint/source/slice
content.  None of the old gauge transition fields are retained. -/
def FiniteColumn.ofCorrelated
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn S) :
    FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax where
  step := S.column.step
  source := S.source
  slice := H.slice
  periodUpper_le := H.periodUpper_le

/-- The row-constructor state at index `n`.  Its path is definitionally the
`n+1` rich-stage increment, which is the triangular coherence needed by the
finite array. -/
def FiniteColumn.state
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n : ℕ) : State where
  start := current (n + 1)
  finish := S.step.next (n + 1)
  path := (S.step.richStage (n + 1)).stage.increment
  P0 := P0 n
  kh := kh n
  khat := khat n
  Qmax := Qmax n
  source := S.source n
  P1 := (S.slice n).periodUpper
  markingLower := (S.slice n).markingLower
  markingUpper := (S.slice n).markingUpper
  facts := Nonaffine.Facts.ofAnalytic (S.slice n) le_rfl

/-- The only additional input to the finite row constructor is the truthful
analytic `Ready` package at each source.  Endpoint coherence remains in
`FiniteColumn.step`; it is not repeated here as a callback. -/
structure ReadyColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) where
  ready : ∀ n, Ready (S.state n)
  initial_range_current : ∀ n,
    range ((ready n).initial).1 = range (S.step.next n).1

noncomputable def ReadyColumn.row
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (n : ℕ) : PresentedRow (S.source n) :=
  Classical.choose ((H.ready n).exists_alignedPresentedRow)

theorem ReadyColumn.row_p_eq_initial
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (n : ℕ) :
    (H.row n).p = (H.ready n).initial :=
  (Classical.choose_spec ((H.ready n).exists_alignedPresentedRow)).1

@[simp] theorem ReadyColumn.row_kFront_eq_zero
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (n : ℕ) : (H.row n).kFront = 0 :=
  (Classical.choose_spec ((H.ready n).exists_alignedPresentedRow)).2

theorem ReadyColumn.row_p_range_current
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (n : ℕ) :
    range ((H.row n).p).1 = range (S.step.next n).1 := by
  rw [H.row_p_eq_initial n]
  exact H.initial_range_current n

def ReadyColumn.nextCurrent
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) : ℕ → Data := fun n => (H.row n).p

theorem ReadyColumn.nextCurrent_range
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (n : ℕ) :
    range (H.nextCurrent n).1 = range (S.step.next n).1 :=
  H.row_p_range_current n

/-- Quantitative bounds used only to type the new rich stages.  The path and
its physical endpoint data are already theorem-produced by `ReadyColumn.row`.
The component transition is deliberately absent. -/
structure RowBounds
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) where
  geometry : ∀ n,
    NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
      (H.row n).output.chosen.Delta
  cost_le : ∀ n, (H.row n).output.chosen.Delta.cost ≤ e n (k + 1)

/-- The next endpoint-coherent column step.  Its stages are assembled from the
actual presented outputs; in particular `increment_cost` is the independent
row cost bound, not the mass of a recursively constructed source. -/
noncomputable def ReadyColumn.successorStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep
      Q H.nextCurrent e (k + 1) P0 P1 khat G1 Cg C c dlt where
  next := fun n => (H.row n).output.jets.rear
  richStage := fun n => by
    let O := (H.row n).output
    exact
      { stage :=
          { increment := O.chosen.Delta
            increment_geometry := B.geometry n
            increment_cost := B.cost_le n
            rear_curve_deriv := O.stage.rear_curve_deriv
            rear_vel_deriv := O.stage.rear_vel_deriv
            rear_periodic := O.stage.rear_periodic
            rear_curvature_nonnegative := O.stage.rear_curvature_nonnegative
            range_edge := by
              have hEdge := O.stage.range_edge
              unfold VariableMarkedTube.GeometricUnitTangentRangeEdge at hEdge ⊢
              exact (H.nextCurrent_range (n + 1)).trans hEdge
            rear_harnack := O.stage.rear_harnack }
        terminalBase := (H.row n).base
        lambda := (H.row n).terminalInput.lambda
        Lambda := (H.row n).terminalInput.Lambda
        marking :=
          { lambda_pos := (H.row n).terminalInput.lambda_pos
            marking := O.marking
            ddpsi := O.ddpsi
            psi_deriv := O.psi_deriv
            dpsi_deriv := O.dpsi_deriv
            ddpsi_cont := O.ddpsi_cont
            psi_zero := O.psi_zero } }

/-- Exact analytic successors for the rows feeding the next correlated column.
The `n+1` shift is the triangular source indexing.  Each bundle retains its
compatibility, recursive analytic facts, and exact density identity. -/
structure SuccessorBundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H) where
  bundle : ∀ n,
    ExactSuccessorBundle (H.row (n + 1)).output.chosen
      (periodLower := P0 n) (kap := kh n)
      (khatNext := khat n) (QmaxNext := Qmax n)
  periodUpper_le : ∀ n, (bundle n).slice.periodUpper ≤ P1 n

/-- The next finite correlated column.  It contains no component transition;
that certificate is paired with the column by the independent all-time stable
component construction. -/
noncomputable def SuccessorBundles.nextColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : SuccessorBundles H B) :
    FiniteColumn Q H.nextCurrent e (k + 1) P0 P1 khat G1 Cg C c dlt kh Qmax where
  step := H.successorStep B
  source := fun n => by
    simpa [ReadyColumn.successorStep] using (X.bundle n).source
  slice := fun n => by
    simpa [ReadyColumn.successorStep] using (X.bundle n).slice
  periodUpper_le := fun n => by
    simpa [ReadyColumn.successorStep] using X.periodUpper_le n

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
