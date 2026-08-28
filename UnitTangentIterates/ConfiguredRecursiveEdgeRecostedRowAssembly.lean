import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectInput
import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow
import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCompositionInvariant

/-!
# Concrete configured recosted row assembly

This joins the uniformly period-scaled physical ancestry to the direct
canonical-density successor.  The returned sigma package is exactly the
input consumed by `ConfiguredRecursiveEdgeRecostedRowState.Direct.Provider`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRowAssembly

open ConfiguredRecursiveEdgeRecostedRowState
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

variable {MA NA Etotal Dtarget K0 K1 K2 Md MP P1 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget)
  {j n depth : ℕ}
  {S : Stage
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)) j}
  {G : GeometricInput S}
  (M : MetricGeometry G)
  (H : ConfiguredRecursiveEdgeChosenMajorSplitHistory.Ancestry
    (K0 := K0) (K1 := K1) (K2 := K2) O G.rawPath n depth)

abbrev scaledDefect : ℝ :=
  ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1)

/-- Assemble the scaled physical row and all qualitative/direct analytic
successor choices. -/
theorem exists_rowInput
    (M : MetricGeometry G)
    (hE : Etotal ≤ 1 / 8)
    (hterminal : H.V depth =
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod S.source) G.rawPath.eta)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t)
    (scalar : Scalar (A := S.source)
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (j + 1))
      (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (j + 1)))
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
          (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature S.source)
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source))
          t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime
          (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source) t| ≤ MP)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        S.source P1)
    (hsourceT : S.Gamma.T = 1)
    (hsmall :
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.chosenJetError
        S.source ≤ 1 / 4) :
    Nonempty
      (Σ R : PhysicalRow S Etotal
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
          (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
                (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
            ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
              (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1)),
        Direct.Input R) := by
  let R := ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow.physicalRow
    (K0 := K0) (K1 := K1) (K2 := K2) O M H hE hterminal hperiod
  obtain ⟨I⟩ :=
    ConfiguredRecursiveEdgeRecostedDirectInput.exists_input_ofSeparated
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) R
      scalar hKnTbd hPtbd separated hsourceT hsmall hperiod
  exact ⟨⟨R, I⟩⟩

/-- Callback-free physical assembly using `ConcreteAncestry`.  The configured
distortion budget, uniformly scaled terminal comparison, and period floor are
all discharged by the ancestry adapter. -/
theorem exists_configuredRowInput
    {MA NA Dtarget K0 K1 K2 Md MP P1 : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal Dtarget)
    {j n depth : ℕ}
    {S : Stage
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
      (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)) j}
    {G : GeometricInput S}
    (M : MetricGeometry G)
    (H : ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow.ConcreteAncestry
      (K0 := K0) (K1 := K1) (K2 := K2) O G n depth)
    (scalar : Scalar (A := S.source)
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (j + 1))
      (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (j + 1)))
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
          (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature S.source)
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source))
          t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime
          (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source) t| ≤ MP)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        S.source P1)
    (hsourceT : S.Gamma.T = 1)
    (hsmall :
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.chosenJetError
        S.source ≤ 1 / 4) :
    Nonempty
      (Σ R : PhysicalRow S
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
          FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
          (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
                (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
            ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
              (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1)),
        Direct.Input R) := by
  let R := ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow.physicalRow
    (K0 := K0) (K1 := K1) (K2 := K2) O M H
  have hkh : 0 < ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
    rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
    norm_num
  have hperiod : ∀ t, 1 ≤ rearPeriod S.source t :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget.one_le_configured_rearPeriod
      hkh
  obtain ⟨I⟩ :=
    ConfiguredRecursiveEdgeRecostedDirectInput.exists_input_ofSeparated
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) R
      scalar hKnTbd hPtbd separated hsourceT hsmall hperiod
  exact ⟨⟨R, I⟩⟩

end ConfiguredRecursiveEdgeRecostedRowAssembly
