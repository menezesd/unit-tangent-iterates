import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

/-!
# Exact analytic successors for presented row families

This removes the independent analytic-successor callback from a presented row
family.  Once the selected rows and their finite scalar envelopes are known,
the exact successor source is chosen by the unconditional chosen-path theorem.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

/-- The finite quantitative inputs for all exact successors of one selected
row family.  These are scalar estimates only; no source or slice is supplied. -/
structure ExactSuccessorInputs
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (rows : (n : ℕ) → PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) where
  sidecars : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars.RecursiveExactSidecars
      (S.source (n + 1))
  periodLower_pos : ∀ n, 0 < P0 n
  periodLower_le : ∀ n, P0 n ≤ (sidecars n).selection.periodLower
  kap_nonnegative : ∀ n, 0 ≤ kh n
  kap_lt_one : ∀ n, kh n < 1
  scalar : ∀ n, Scalar (A := S.source (n + 1)) (kap := kh n)
    (P0Next := P0 n) (khatNext := khat n) (QmaxNext := Qmax n)

/-- Select the exact recursive analytic successor at one row index, using the
fresh bounds stored by the current source rather than external envelopes. -/
noncomputable def ExactSuccessorInputs.recursiveAnalytic
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    {rows : (n : ℕ) → PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (I : ExactSuccessorInputs rows) (n : ℕ) :
    RecursiveAnalyticSuccessor (rows (n + 1)).output.chosen.Delta
      (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n) :=
  Classical.choice (ChosenPath.exists_recursiveAnalyticSuccessor
    (rows (n + 1)).output.chosen
    (I.periodLower_pos n) (I.kap_nonnegative n) (I.kap_lt_one n)
    (fun t => (I.periodLower_le n).trans ((I.sidecars n).selection.period_lower t))
    (I.sidecars n).selection.period_upper
    (I.sidecars n).selection.normalizedCurvatureTime_le
    (I.sidecars n).selection.periodTime_le (I.scalar n))

/-- Forget the recursive sidecars for consumers of the legacy row-family API. -/
noncomputable def ExactSuccessorInputs.analytic
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    {rows : (n : ℕ) → PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (I : ExactSuccessorInputs rows) (n : ℕ) :
    AnalyticSuccessor (rows (n + 1)).output.chosen.Delta
      (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n) :=
  (I.recursiveAnalytic n).toAnalytic

/-- A presented row family which does not erase the exact recursive source
package selected for the following depth. -/
structure RecursivePresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2) where
  row : ∀ n, PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  recursiveAnalytic : ∀ n, RecursiveAnalyticSuccessor
    (row (n + 1)).output.chosen.Delta (S.source (n + 1))
    (P0 n) (kh n) (khat n) (Qmax n)

def RecursivePresentedRowFamily.toPresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (F : RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  row := F.row
  analytic := fun n => (F.recursiveAnalytic n).toAnalytic

noncomputable def RecursivePresentedRowFamily.successor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (F : RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  F.toPresentedRowFamily.successor

@[simp] theorem RecursivePresentedRowFamily.mappedSource_eq
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (F : RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    F.successor.mappedColumn.source n = (F.recursiveAnalytic n).source := by
  rfl

/-- Exact successor inputs produce the non-erasing recursive family directly. -/
noncomputable def ExactSuccessorInputs.recursiveRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    {rows : (n : ℕ) → PresentedRowSelection (n := n)
      (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (I : ExactSuccessorInputs rows) :
    RecursivePresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  row := rows
  recursiveAnalytic := I.recursiveAnalytic

/-- Assemble a full presented row family with no analytic successor callback. -/
noncomputable def ExactSuccessorInputs.rowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    {rows : (n : ℕ) → PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (I : ExactSuccessorInputs rows) :
    PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  I.recursiveRowFamily.toPresentedRowFamily

/-- Select every presented row from its concrete construction. -/
noncomputable def selectedRows
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (R : (n : ℕ) → PresentedRowConstruction (n := n)
      (a := a) (MA := MA) (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S)
    (n : ℕ) : PresentedRowSelection (n := n)
      (a := a) (MA := MA) (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S :=
  (R n).selection

/-- Concrete row constructions plus scalar exact-successor inputs produce the
entire row family. -/
noncomputable def rowFamilyOfConstructions
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {periodRow : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      periodRow diagonal kh Qmax K0 K1 K2}
    (R : (n : ℕ) → PresentedRowConstruction (n := n)
      (a := a) (MA := MA) (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S)
    (I : ExactSuccessorInputs (selectedRows R)) :
    PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  I.rowFamily

end FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider
