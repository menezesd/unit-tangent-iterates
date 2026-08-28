import UnitTangentIterates.FiniteNonaffineMajorNormalizedState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedNormalizedReachableState

/-! # Recharging a depth-zero normalized state to an explicit major -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace FiniteNonaffineMajorDepthZeroOfLegacy

open FiniteHistoryMajorBudget
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {MA NA Etotal Dtarget : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
  {P0u khatu Qmaxu : ℕ → ℝ} {r : ℕ}
  {S : Stage P0u
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    khatu Qmaxu r}
  {P1 edgeDefect : ℝ}

/-- A depth-zero ancestry has no transition links, so its component endpoint
data can be installed over any explicit major without changing mathematics. -/
noncomputable def ancestry
    (B : MajorBudget Etotal)
    (A : ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.ConcreteAncestry
      (O := O) S.Gamma 0 edgeDefect) :
    FiniteNonaffineMajorHistory.ConcreteAncestry B S.Gamma 0 edgeDefect where
  ancestry :=
    { V := A.ancestry.V
      baseJ := A.ancestry.baseJ
      baseP := A.ancestry.baseP
      baseEta := A.ancestry.baseEta
      base_eq := A.ancestry.base_eq
      d_nonnegative := A.ancestry.d_nonnegative
      components_nonnegative := A.ancestry.components_nonnegative
      initial_le := A.ancestry.initial_le
      links := by intro j hj; omega }
  terminalJ := A.terminalJ
  terminalP := A.terminalP
  terminal_eq := A.terminal_eq

/-- Copy every analytic field of a legacy depth-zero normalized state and
replace only its major bookkeeping by an explicit budget. -/
noncomputable def state
    (B : MajorBudget Etotal)
    (A : ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State
      O S P1 0 edgeDefect)
    (heps : A.sourceFacts.eps ≤ B.major 0) :
    FiniteNonaffineMajorNormalizedState.State B
      (S := S) (P1 := P1) (depth := 0) (edgeDefect := edgeDefect) where
  sourceFacts :=
    { slice := A.sourceFacts.slice
      periodUpper_le := A.sourceFacts.periodUpper_le
      functional := A.sourceFacts.functional
      eps := A.sourceFacts.eps
      jets := A.sourceFacts.jets
      eps_le_major := heps }
  intrinsic := A.intrinsic
  periodFloor := A.periodFloor
  ancestry := ancestry B A.ancestry
  terminalJ_eq := by simpa [ancestry] using A.terminalJ_eq
  terminalP_eq := by simpa [ancestry] using A.terminalP_eq

end FiniteNonaffineMajorDepthZeroOfLegacy
