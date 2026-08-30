import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedProvenance
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-! # Depth-one source-mass provenance over the prepared base -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteBasePreparedProvenance

open ConfiguredRecursiveEdgeRecostFinitePreparedProvenance
  ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic
  ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R) {K0 K1 K2 : ℝ}

set_option maxHeartbeats 2000000

/-- The unconditional first prepared step, retaining only the sharp source-mass
allowance needed to continue the recursion from depth one. -/
noncomputable def firstEnrichedReachable : EnrichedReachable H 1 := by
  let S := preparedStep (K0 := K0) (K1 := K1) (K2 := K2) H
  refine
    { reachable := S.next H
      configured :=
        ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData.nextConfigured H
          S.input
      geometry :=
        ConfiguredRecursiveEdgeRecostFinitePreparedNextGeometry.nextGeometry H S (fun n => by
        change
          FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
              (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2)
                H n).source ≤ _
        refine (basePreparedAnalytic_sourceMass_le_allowance
          (K0 := K0) (K1 := K1) (K2 := K2) H n).trans_eq ?_
        simp only
          [ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.data,
            ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.data,
            ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
            ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data]
        simp_rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
        simp [ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
      rearCurvature_le := by
        intro n t s
        change
          |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
            (S.input.analytic (n + 1)).source t s| ≤
              ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
        exact S.mappedRearCurvature_le (n + 1) t s
      sourceMass_le_allowance := by
        intro n
        change
          FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
              (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2)
                H (n + 1)).source ≤
            multiplierRecostSourceAllowance H.data
              ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
              ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
              ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
              ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
              (n + 1 + 1)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (basePreparedAnalytic_sourceMass_le_allowance
            (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)) }

end ConfiguredRecursiveEdgeRecostFiniteBasePreparedProvenance
