import UnitTangentIterates.PhysicalArclengthJacobiTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

/-!
# Alignment of constant-period physical component conventions

The configured base column records the physical-arclength components with a
single physical period.  The fully physical transition records the same
quantities with the period retained inside the time integrals.  This module
exposes their exact agreement when that period function is constant.
-/

noncomputable section

open MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalComponentAlignment

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

/-- The fully physical convention specializes exactly to the constant-period
physical-arclength convention. -/
theorem fullyPhysical_const_eq_physicalArclength
    (P : ℝ) (eta : ℝ → ℝ → ℝ) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (fun _ ↦ P) eta =
      PhysicalArclengthJacobiTransition.components P eta := by
  simp [FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents,
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS1,
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS2,
    VariableArclengthScaledJacobiTransition.physicalW,
    PhysicalArclengthJacobiTransition.components, W, S]

/-- At unit period, the terminal convention used by finite stability is the
same constant-period physical-arclength convention. -/
theorem physicalArclength_one_eq_terminal
    (eta : ℝ → ℝ → ℝ) :
    PhysicalArclengthJacobiTransition.components 1 eta =
      ArclengthScaledJacobiTransition.physicalComponents 1 eta := by
  simp [PhysicalArclengthJacobiTransition.components,
    ArclengthScaledJacobiTransition.physicalComponents]

end ConfiguredRecursiveEdgePhysicalComponentAlignment
