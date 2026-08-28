import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings

/-!
# Configured intrinsic rear-period floor

The paper's fixed steering threshold is `5 / 6`.  At this value the uniform
intrinsic rear-period lower bound is larger than one.  This is the numerical
fact needed to compare the normalized second spatial component after the
chosen time-dependent marking.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRearPeriodFloor

open FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareAppliedSource

/-- The configured intrinsic rear period is uniformly at least one. -/
theorem one_le_rearPeriodFloor_sourceKh :
    1 <= rearPeriodFloor
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  have hkh :
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh =
        (5 / 6 : ℝ) := by
    norm_num [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh,
      TubeConstants.khat]
  have hsqrt : (1 / 2 : ℝ) <= Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hfront : (2 : ℝ) <= 2 * Real.pi / (5 / 6 : ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hmul :
      (1 / 2 : ℝ) * 2 <=
        Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) *
          (2 * Real.pi / (5 / 6 : ℝ)) :=
    mul_le_mul hsqrt hfront (by norm_num) (Real.sqrt_nonneg _)
  rw [hkh]
  simpa [rearPeriodFloor, frontPeriodFloor] using hmul

/-- Every configured marking-aware source inherits the numerical unit rear
period floor, uniformly in time. -/
theorem one_le_rearPeriod
    {p q : Data} {Gamma : NormalPath p q}
    {P0 khat Qmax : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource Gamma P0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax}
    (t : ℝ) : 1 <= rearPeriod A t := by
  apply one_le_rearPeriodFloor_sourceKh.trans
  apply
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.rearPeriodFloor_le
  norm_num [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh,
    TubeConstants.khat]

end ConfiguredRecursiveEdgeRearPeriodFloor
