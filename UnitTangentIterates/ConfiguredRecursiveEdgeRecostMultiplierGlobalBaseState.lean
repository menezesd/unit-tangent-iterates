import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedGeometricState

/-! # Truthful global physical base state for the multiplier recursion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState

open ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant
  ConfiguredRecursiveEdgeRecostedGeometricState
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

abbrev data
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0) :=
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar

def baseError
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgePhysicalCompositionBase.compositionError J n 1

def sourceError
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (n depth : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant.hybridErrorTable
    (baseError J) (data J)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2 n depth

/-- The global physical column is kept at its original row indices.  Only its
phantom recursive source-error table is changed, with depth one left equal to
the theorem-produced physical composition bound. -/
noncomputable def state (R : RecostClosingOutput J O) :
    State (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Q J.scalar)
      (sourceError J)
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (data J))
      (ConfiguredRecursiveEdgeSourceP0Growth.edgeP1 (data J)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (ConfiguredRecursiveEdgeSourceP0Growth.edgeG1 (data J)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (ConfiguredRecursiveEdgeSourceP0Growth.edgeCgWithKhat (data J)
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax J.scalar)
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar)
      (ConfiguredCanonicalPairSource.commonC (data J))
      (ConfiguredCanonicalPairSource.commonDlt (data J))
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh where
  current := baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2)
  depth := 0
  column := ConfiguredRecursiveEdgeRecostedCompositionInvariant.relabelColumn
    (e' := sourceError J)
    (base J (K0 := K0) (K1 := K1) (K2 := K2))
  invariant := withHybridBase (baseError J) (data J)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
    (base J (K0 := K0) (K1 := K1) (K2 := K2))
    (invariant J (K0 := K0) (K1 := K1) (K2 := K2)) (by
      intro n
      exact (invariant J (K0 := K0) (K1 := K1)
        (K2 := K2)).source_cost_le n)

@[simp] theorem state_depth (R : RecostClosingOutput J O) :
    (state (K0 := K0) (K1 := K1) (K2 := K2) R).depth = 0 := rfl

/-- Selecting only the final-tail rows recovers the configured public base. -/
theorem state_public_displayed
    (R : RecostClosingOutput J O) (n : ℕ) :
    ((state (K0 := K0) (K1 := K1) (K2 := K2) R).stage
      (R.totalShift + n)).displayed =
        ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R n := by
  rfl

end ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState
