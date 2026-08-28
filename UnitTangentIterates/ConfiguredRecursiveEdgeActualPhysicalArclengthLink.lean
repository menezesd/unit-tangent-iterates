import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalHistory

/-!
# Fully physical links in compatible arclength representatives

The paper transports every inverse-Jacobi path in intrinsic arclength and
uses only constant arclength shifts between adjacent rows.  Those shifts leave
all four physical components unchanged.  Consequently the two comparison
maps around the intrinsic Jacobi transition are identities; no nonaffine
normalized-jet distortion is needed at this layer.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeActualPhysicalArclengthLink

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeActualPhysicalHistory
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

/-- Identity comparison from a compatible arclength source representative to
the intrinsic front. -/
def sourceIdentity (C : Components) :
    SourceIntrinsicComparison C C 1 where
  w := le_rfl
  s0 := le_rfl
  s1 := by simp

/-- Identity comparison from the intrinsic rear to its compatible arclength
target representative. -/
def targetIdentity (C : Components) :
    TargetMarkingComparison C C 1 0 where
  w := le_rfl
  s0 := le_rfl
  s1 := by simp
  s2 := by simp

/-- A theorem-produced inverse-Jacobi row, read in compatible intrinsic
arclength representatives, is a concrete paired link with zero marking
errors.  The ambient majorant may remain larger; its nonnegativity supplies
the two scalar inclusions. -/
def pairedLinkOfFullyPhysicalArclength
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (applied : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A)
    {major : ℕ → ℝ} {j : ℕ}
    (hkh : 0 < kh)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        A P1)
    (integrable :
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (hprev : 0 ≤ FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.previousMajor
      major j)
    (hcur : 0 ≤ major j)
    (hadjacent :
      FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.previousMajor
        major j + major j ≤ 1 / 4) :
    PairedLink
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      major j
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  apply PairedLink.ofFullyPhysical applied hkh separated integrable
    (epsPrev := 0) (epsCur := 0)
  · exact le_rfl
  · exact le_rfl
  · simpa using hprev
  · simpa using hcur
  · exact hadjacent
  · simpa using sourceIdentity
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
  · simpa using targetIdentity
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))

end ConfiguredRecursiveEdgeActualPhysicalArclengthLink
