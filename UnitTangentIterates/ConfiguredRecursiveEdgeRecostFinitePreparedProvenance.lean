import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedStep
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextGeometry
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-! # Source-mass provenance for finite prepared reachability -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedProvenance

open ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedNextGeometry
  ConfiguredRecursiveEdgeRecostFinitePreparedStep
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- A prepared reachable layer together with the direct source-mass
provenance for its successor-indexed rows. -/
structure EnrichedReachable (k : ℕ) where
  reachable : PreparedReachable H k
  configured : ∀ n,
    ConfiguredNode H.toClosing (n + k) (reachable.nodes n)
  geometry : PreparedGeometryProvenance H k reachable
  rearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (sourceNode H reachable n).stage.source t s| ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
  sourceMass_le_allowance : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (reachable.nodes (n + 1)).stage.source ≤
      multiplierRecostSourceAllowance H.data
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
        (n + k + 1)

namespace EnrichedReachable

variable {k : ℕ}

/-- The analytic bridge data carried structurally by an enriched layer. -/
noncomputable def bridgeData (E : EnrichedReachable H k) :
    BridgeData H E.reachable where
  configured := E.configured
  geometry := E.geometry
  rearCurvature_le := E.rearCurvature_le
  sourceMass_le_allowance := E.sourceMass_le_allowance

end EnrichedReachable

/-- A prepared step carrying exactly the mass estimate proved for each of
its newly constructed analytic sources. -/
structure EnrichedStepData {k : ℕ} (Z : EnrichedReachable H k) where
  data : PreparedStepData H Z.reachable
  sourceMass_le_allowance : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (data.input.analytic n).source ≤
      multiplierRecostSourceAllowance H.data
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
        (n + k + 1)
  sourceMass_le_allowance_shifted : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (data.input.analytic n).source ≤
      multiplierRecostSourceAllowance O.data
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
        (H.toClosing.preShift + H.toClosing.large.N +
          (n + (k + 1)))

namespace EnrichedReachable

variable {k : ℕ}

/-- The unconditional prepared step canonically determined by an enriched
reachable layer, with both forms of its source-mass allowance retained. -/
noncomputable def stepData (E : EnrichedReachable H k) :
    EnrichedStepData H E where
  data := preparedStep H (bridgeData H E)
  sourceMass_le_allowance :=
    preparedAnalytic_sourceMass_le_allowance H (bridgeData H E)
  sourceMass_le_allowance_shifted :=
    inputData_sourceMass_le_allowance H (bridgeData H E)

end EnrichedReachable

namespace EnrichedStepData

variable {k : ℕ} {Z : EnrichedReachable H k}

/-- The next prepared layer inherits only the direct estimate for the
analytic source that definitionally becomes its successor-indexed node. -/
noncomputable def next (data : EnrichedStepData H Z) :
    EnrichedReachable H (k + 1) where
  reachable := data.data.next H
  configured := InputData.nextConfigured H data.data.input
  geometry := nextGeometry H data.data
    data.sourceMass_le_allowance_shifted
  rearCurvature_le n t s := by
    change
      |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
        (data.data.input.analytic (n + 1)).source t s| ≤
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    exact data.data.mappedRearCurvature_le (n + 1) t s
  sourceMass_le_allowance n := by
    change
      FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
          (data.data.input.analytic (n + 1)).source ≤
        multiplierRecostSourceAllowance H.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (n + (k + 1) + 1)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      data.sourceMass_le_allowance (n + 1)

end EnrichedStepData

end ConfiguredRecursiveEdgeRecostFinitePreparedProvenance
