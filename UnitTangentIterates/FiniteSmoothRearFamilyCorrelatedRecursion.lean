import UnitTangentIterates.FiniteSmoothRearFamilyAnalyticSource

/-!
# Source-preserving finite rear-family recursion

The ordinary mapped-column API retains the selected geometric and physical
outputs but forgets the analytic source needed to apply the long rear-family
theorem again.  This module carries that source across the successor step.
It adds no existence callback: `row` is the already constructed enriched row,
and `successorSource` is analytic input for its next selected-rear image.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyCorrelatedRecursion

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyEnrichedMapProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- A rowwise mapped-column construction which also retains the analytic
source required at the following recursive depth. -/
structure Provider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  row : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ),
    RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2
      S.column.step n
  successorSource : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ),
    Source ((row S (n + 1)).output.Delta)
      (P0 n) (kh n) (khat n) (Qmax n)

/-- Select the successor once and retain exactly the source belonging to its
`(n+1)`-st rich row. -/
def mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) :
    CorrelatedColumn Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2 := by
  let W := fun n => G.row S n
  let T := mappedColumnOfRows S.column W
  refine
    { column := T.val
      source := fun n => ?_ }
  simpa [T, mappedColumnOfRows, W] using G.successorSource S n

end FiniteSmoothRearFamilyCorrelatedRecursion
