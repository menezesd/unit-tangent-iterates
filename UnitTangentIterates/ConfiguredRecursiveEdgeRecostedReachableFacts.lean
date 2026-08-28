import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant

/-! # Reachable nonaffine source facts for direct-recost recursion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedReachableFacts

open ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA Etotal Dtarget : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}

/-- The source-side state needed by one normalized nonaffine history link.
The current source error is charged to the predecessor slot at link `j`. -/
structure SourceFacts
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      RJ Etotal Dtarget)
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (P1 : ℝ) (j : ℕ) where
  slice :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts A
  periodUpper_le : slice.periodUpper ≤ P1
  functional :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta
  eps : ℝ
  jets :
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.SourceNormalizedJetBounds A eps
  eps_le_major : eps ≤ O.major j

namespace SourceFacts

def nonaffine
    (F : SourceFacts O A P1 j) :
    FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts
      A P1 F.slice.markingLower F.slice.markingUpper :=
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts.ofAnalytic
    F.slice F.periodUpper_le

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {r : ℕ}
  {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
    P0u khu khatu Qmaxu r}
  {E C0 C1 C2 d p0 kh0 khat0 qmax0 P1 : ℝ}
  {R : ConfiguredRecursiveEdgeRecostedCarrierRow.CarrierRow
    S E C0 C1 C2 d}

/-- Propagate the complete reachable-source state to the direct recost
successor.  Only the configured period ceiling and current major comparison
are scalar inputs; regularity, functional integrability, and predecessor jets
are retained by `Input`. -/
def ofInput
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      RJ Etotal Dtarget)
    (I : Input R p0 kh0 khat0 qmax0) (j : ℕ)
    (hP1 : I.slice.periodUpper ≤ P1)
    (heps : I.eps ≤ O.major (j + 1)) :
    SourceFacts O I.source P1 (j + 1) where
  slice := I.slice
  periodUpper_le := hP1
  functional := I.targetFunctional
  eps := I.eps
  jets := I.sourceJets
  eps_le_major := heps

end SourceFacts

end ConfiguredRecursiveEdgeRecostedReachableFacts
