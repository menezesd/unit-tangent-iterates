import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-! # Source-mass bound for the configured depth-zero finite column -/

noncomputable section

open PathMetric

namespace ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnBase
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

variable {MA NA : ℝ}

/-- The configured depth-zero source carries exactly the mass budget already
charged to the successor-indexed composition error. -/
theorem sourceMass_le_compositionError
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n) ≤
      compositionError J n 1 := by
  simpa [sourceMass, column] using
    (compositionBase_source_cost_le J
      (K0 := K0) (K1 := K1) (K2 := K2) n)

/-- Definitionally, the preceding budget is the configured composition
physical defect at the source's successor row. -/
theorem sourceMass_le_compositionPhysicalDefect
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n) ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionPhysicalDefect
        (D J.scalar) (n + 1) := by
  simpa [compositionError,
    ConfiguredDiagonalStableRowDefectProvider.error] using
    (sourceMass_le_compositionError J
      (K0 := K0) (K1 := K1) (K2 := K2) n)

end ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
