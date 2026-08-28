import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRegularitySum
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

/-!
# Recursive exact sidecars

The first-order exact sidecars of a source are enough to use that source once.
Recursion additionally needs fresh finite bounds for selecting the intrinsic
successor front of the same source.  This strengthened package keeps those
quantities source-tied and prevents predecessor bounds from being reused at
the wrong index.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

/-- Exact regularity plus the fresh quantitative inputs needed at the next
selection. -/
structure RecursiveExactSidecars
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Type where
  regularity : ExactSidecars A
  selection : SelectionBounds A

/-- The ordinary exact regularity fields are automatic once the fresh
selection bounds have been established. -/
def RecursiveExactSidecars.ofSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (selection : SelectionBounds A) : RecursiveExactSidecars A where
  regularity := ExactSidecars.ofSource A
  selection := selection

end FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

