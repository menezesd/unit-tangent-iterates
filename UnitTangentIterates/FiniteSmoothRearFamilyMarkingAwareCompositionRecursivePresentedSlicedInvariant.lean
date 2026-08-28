import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

/-! # Composition-stable reachable presented columns -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Rows whose exact analytic successors retain the composition-density
budgets needed at the following depth. -/
structure CompositionRecursivePresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  row : ∀ n, PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  compositionAnalytic : ∀ n, CompositionRecursiveAnalyticSuccessor
    (row (n + 1)).output.chosen.Delta (S.source (n + 1))
    (P0 n) (kh n) (khat n) (Qmax n)
  /-- The source installed at mapped row `n` starts at the rear selected in
  the adjacent row `n`.  This is a cross-row marking statement and is not a
  consequence of the isolated analytic-successor record. -/
  mappedInitialAlignment : ∀ n u,
    RearOwnArclength.rearOwn (compositionAnalytic n).source.F
      (compositionAnalytic n).source.Theta
      (compositionAnalytic n).source.delta
      (compositionAnalytic n).source.sf 0
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (compositionAnalytic n).source 0 * u) =
      (row n).output.jets.rear.1 u
  /-- The quantitative mass bound consumed by the following recursive depth. -/
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(row (n + 1)).output.chosen.Delta.T,
      (compositionAnalytic n).source.m t) ≤ e n ((k + 1) + 1)

def CompositionRecursivePresentedRowFamily.toRecursive
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : CompositionRecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  row := F.row
  recursiveAnalytic := fun n ↦ (F.compositionAnalytic n).toRecursiveAnalyticSuccessor

def CompositionRecursivePresentedRowFamily.successor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : CompositionRecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  F.toRecursive.successor

/-- Reachable columns retain the two source-density inequalities in addition
to the ordinary exact slice/spatial invariant. -/
structure CompositionRecursiveSlicedCorrelatedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    extends RecursiveSlicedCorrelatedColumn S where
  initialAlignment : ∀ n u,
    RearOwnArclength.rearOwn (S.source n).F (S.source n).Theta
      (S.source n).delta (S.source n).sf 0
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (S.source n) 0 * u) = (S.column.step.next n).1 u
  source_cost_le : ∀ n,
    (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
      (S.source n).m t) ≤ e n (k + 1)
  composition_d1 : ∀ n t,
    2 * ((S.column.step.richStage (n + 1)).stage.increment.m t /
        Real.sqrt (1 - (kh n) ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
        (∫ s in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m s) ≤ (S.source n).m t
  composition_d2 : ∀ n t,
    ((S.source n).Dd t +
        2 * ((S.column.step.richStage (n + 1)).stage.increment.m t /
          Real.sqrt (1 - (kh n) ^ 2))) *
        GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
          (∫ s in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
            (S.source n).m s) ^ 2 +
      2 * ((S.column.step.richStage (n + 1)).stage.increment.m t /
          Real.sqrt (1 - (kh n) ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod (S.source n) 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
          (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n))
          (∫ s in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
            (S.source n).m s) ≤ (S.source n).m t

/-- A composition-stable row family preserves the strengthened invariant. -/
def CompositionRecursivePresentedRowFamily.mappedInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : CompositionRecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (hperiod : ∀ n, (F.compositionAnalytic n).slice.periodUpper ≤ P1 n) :
    CompositionRecursiveSlicedCorrelatedColumn F.successor.mappedColumn where
  toRecursiveSlicedCorrelatedColumn :=
    RecursivePresentedRowFamily.mappedInvariant F.toRecursive
      (fun n ↦ by simpa using hperiod n)
  initialAlignment := fun n u ↦ by
    simpa [CompositionRecursivePresentedRowFamily.successor,
      RecursivePresentedRowFamily.successor,
      RecursivePresentedRowFamily.toPresentedRowFamily,
      PresentedRowFamily.successor, successorOfPresentedRows] using
      F.mappedInitialAlignment n u
  source_cost_le := fun n ↦ by
    simpa using F.mappedCost_le n
  composition_d1 := fun n t ↦ by
    simpa using (F.compositionAnalytic n).composition_d1 t
  composition_d2 := fun n t ↦ by
    simpa using (F.compositionAnalytic n).composition_d2 t

/-- An invariant-indexed provider which can only be applied to reachable
composition-stable columns. -/
structure CompositionRecursivePresentedSlicedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  rows : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    CompositionRecursiveSlicedCorrelatedColumn S →
      CompositionRecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
        (K0 := K0) (K1 := K1) (K2 := K2) S
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : CompositionRecursiveSlicedCorrelatedColumn S) n,
    ((rows S H).compositionAnalytic n).slice.periodUpper ≤ P1 n

structure CompositionRecursivePresentedSlicedState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (K0 K1 K2 : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  invariant : CompositionRecursiveSlicedCorrelatedColumn column

def CompositionRecursivePresentedSlicedState.next
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : CompositionRecursivePresentedSlicedProvider Q e P0 P1 khat G1 Cg C
      c dlt period diagonal kh Qmax a MA NA K0 K1 K2)
    (X : CompositionRecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C
      c dlt period diagonal kh Qmax K0 K1 K2) :
    CompositionRecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C
      c dlt period diagonal kh Qmax K0 K1 K2 := by
  let F := G.rows X.column X.invariant
  exact
    { current := X.column.column.step.next
      depth := X.depth + 1
      column := F.successor.mappedColumn
      invariant := F.mappedInvariant
        (G.mappedPeriodUpper_le X.column X.invariant) }

/-- One base invariant and the invariant-indexed provider determine the entire
composition-stable recursive construction. -/
structure CompositionRecursivePresentedConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  current0 : ℕ → Data
  base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseInvariant : CompositionRecursiveSlicedCorrelatedColumn base
  base_eq : ∀ n, base.column.step.next n = Q n
  provider : CompositionRecursivePresentedSlicedProvider Q e P0 P1 khat G1 Cg C
    c dlt period diagonal kh Qmax a MA NA K0 K1 K2

def CompositionRecursivePresentedConstructionCore.initialState
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : CompositionRecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C
      c dlt period diagonal kh Qmax a MA NA K0 K1 K2) :
    CompositionRecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2 where
  current := F.current0
  depth := 0
  column := F.base
  invariant := F.baseInvariant

end FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
