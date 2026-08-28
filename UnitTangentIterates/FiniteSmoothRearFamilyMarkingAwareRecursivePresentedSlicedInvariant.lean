import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider

/-! # Recursive source invariants on reachable presented columns -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareSource

/-- The exact source data needed to apply terminal geometry at every reachable
row.  Unlike a total provider, this invariant is required only on columns
actually produced by the recursion. -/
structure RecursiveSlicedCorrelatedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) extends SlicedCorrelatedColumn S where
  spatial : ∀ n, SpatialFrameRegularity
    (S.column.step.richStage (n + 1)).stage.increment
    (S.source n).Ydot (S.source n).Theta (S.source n).delta
    (S.source n).sf (S.source n).P (S.source n).m (kh n) (Qmax n)
  sidecars : ∀ n, RecursiveExactSidecars (S.source n)
  terminalCurvature_nonnegative : ∀ n s,
    0 ≤ (S.source n).K
      (S.column.step.richStage (n + 1)).stage.increment.T s
  terminalRange : ∀ n,
    range ((S.source n).F
      (S.column.step.richStage (n + 1)).stage.increment.T) =
      range (S.column.step.next (n + 1)).1

/-- A non-erasing recursive row family preserves the complete reachable
source invariant.  Only the already-existing common period ceiling is needed
to package the inherited slice. -/
def RecursivePresentedRowFamily.mappedInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (hperiod : ∀ n, (F.recursiveAnalytic n).slice.periodUpper ≤ P1 n) :
    RecursiveSlicedCorrelatedColumn F.successor.mappedColumn where
  slice := fun n => by
    simpa using (F.recursiveAnalytic n).slice
  periodUpper_le := fun n => by
    simpa using hperiod n
  spatial := fun n => by
    simpa using (F.recursiveAnalytic n).spatial
  sidecars := fun n => by
    simpa using (F.recursiveAnalytic n).sidecars
  terminalCurvature_nonnegative := fun n s => by
    simpa using (F.recursiveAnalytic n).terminalCurvature_nonnegative s
  terminalRange := fun n => by
    simpa using (F.recursiveAnalytic n).terminalRange

/-- An all-depth provider on the exact invariant-carrying reachable state. -/
structure RecursivePresentedSlicedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  rows : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    RecursiveSlicedCorrelatedColumn S →
      RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
        (K0 := K0) (K1 := K1) (K2 := K2) S
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : RecursiveSlicedCorrelatedColumn S) n,
    ((rows S H).recursiveAnalytic n).slice.periodUpper ≤ P1 n

structure RecursivePresentedSlicedState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (K0 K1 K2 : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  invariant : RecursiveSlicedCorrelatedColumn column

def RecursivePresentedSlicedState.next
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : RecursivePresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (X : RecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) :
    RecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2 := by
  let F := G.rows X.column X.invariant
  exact
    { current := X.column.column.step.next
      depth := X.depth + 1
      column := F.successor.mappedColumn
      invariant := RecursivePresentedRowFamily.mappedInvariant F
        (G.mappedPeriodUpper_le X.column X.invariant) }

/-- A recursive presented construction starts from one genuine invariant and
iterates only through invariant-preserving selected successors. -/
structure RecursivePresentedConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  current0 : ℕ → Data
  base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseInvariant : RecursiveSlicedCorrelatedColumn base
  base_eq : ∀ n, base.column.step.next n = Q n
  provider : RecursivePresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2

namespace RecursivePresentedConstructionCore

def initialState
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    RecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2 where
  current := F.current0
  depth := 0
  column := F.base
  invariant := F.baseInvariant

def state
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) : ℕ →
    RecursivePresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2
  | 0 => F.initialState
  | k + 1 => RecursivePresentedSlicedState.next F.provider (F.state k)

@[simp] theorem state_depth
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :
    (F.state k).depth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [state, RecursivePresentedSlicedState.next, ih]

end RecursivePresentedConstructionCore

end FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
