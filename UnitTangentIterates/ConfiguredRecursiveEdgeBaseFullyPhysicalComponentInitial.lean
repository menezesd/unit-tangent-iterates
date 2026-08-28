import UnitTangentIterates.ConfiguredRecursiveEdgeBasePhysicalComponentInitial
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalComponentAlignment

/-!
# Fully physical initial bound for the configured base source

The physical perimeter carried by the configured base source is the constant
model-row perimeter.  Thus its time-varying fully physical components are
exactly the scalar physical-arclength components already bounded by the base
column.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  EnrichedPhysicalChosenRichFamily

variable {MA NA K0 K1 K2 : ℝ}

private theorem physicalRigidFields_period
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    (FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields
      A a w hw).P = A.P := by
  simp [FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields]

/-- The configured base source at row `n` retains the constant physical
period of the rich stage at diagonal `n + 1`. -/
theorem physicalBaseSource_period_eq
    (J : RowJetScalarOutput MA NA) (n : ℕ) :
    (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
      J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
        (K0 := K0) (K1 := K1) (K2 := K2) n).P =
      fun _ ↦ period J.scalar (n + 1) 0 := by
  funext t
  simp only [ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput]
  rw [physicalRigidFields_period]
  simp only [id_eq]
  rw [FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.phaseRigid_P,
    ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgeSourceAt_period_eq]
  simp [ConfiguredBaseInterpolationShiftedFront.period, period,
    ConfiguredEnrichedConstructionCoreProvider.period,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D]

/-- Exact fully physical initial estimate for the source/path pair used by
the first inverse-Jacobi link of the configured base edge. -/
theorem base_fullyPhysical_components_le_edgePhysicalDefect
    (J : RowJetScalarOutput MA NA) (n : ℕ) :
    let B := baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)
    let A := B.source n
    let V :=
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P (B.column.step.richStage (n + 1)).stage.increment.eta
    V.w ≤ edgePhysicalDefect (D J.scalar) (n + 1) ∧
      V.s0 ≤ edgePhysicalDefect (D J.scalar) (n + 1) ∧
      V.s1 ≤ edgePhysicalDefect (D J.scalar) (n + 1) ∧
      V.s2 ≤ edgePhysicalDefect (D J.scalar) (n + 1) := by
  dsimp only
  rw [baseCorrelated_source, physicalBaseSource_period_eq]
  rw [ConfiguredRecursiveEdgePhysicalComponentAlignment.fullyPhysical_const_eq_physicalArclength]
  simpa using
    (ConfiguredRecursiveEdgeBasePhysicalComponentInitial.base_components_le_edgePhysicalDefect
      (K0 := K0) (K1 := K1) (K2 := K2) J (n + 1))

end ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial
