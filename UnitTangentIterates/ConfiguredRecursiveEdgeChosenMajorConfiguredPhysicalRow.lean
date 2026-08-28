import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow
import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget

/-! # Callback-free configured physical rows from exact chosen ancestry -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeChosenMajorSplitHistory
  ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  ConfiguredRecursiveEdgeRecostedRowState
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal Dtarget)
  {j n depth : ℕ}
  {S : Stage
    (edgeSourceP0
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (fun _ ↦ sourceKh)
    (fun _ ↦ analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)) j}
  {G : GeometricInput S}

/-- A chosen ancestry whose final existential link is identified with the
current direct row.  These are structural equalities, not analytic
callbacks: its source has the current rear-period function and its chosen
target has the current chosen eta field. -/
structure ConcreteAncestry (G : GeometricInput S) (n depth : ℕ) where
  ancestry : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
    O G.rawPath n (depth + 1)
  last_period_eq :
    rearPeriod
        ((ancestry.links depth (Nat.lt_succ_self depth)).source) =
      rearPeriod S.source
  last_chosen_eta_eq :
    (ancestry.links depth
        (Nat.lt_succ_self depth)).chosen.Delta.eta =
      G.output.chosen.Delta.eta

namespace ConcreteAncestry

/-- The last exact chosen-link identity supplies the terminal fully physical
component identity needed by uniform terminal scaling. -/
theorem terminal_eq
    (H : ConcreteAncestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G n depth) :
    H.ancestry.V (depth + 1) =
      physicalComponents (rearPeriod S.source) G.rawPath.eta := by
  let L := H.ancestry.links depth (Nat.lt_succ_self depth)
  calc
    H.ancestry.V (depth + 1) =
        physicalComponents (rearPeriod L.source) L.chosen.Delta.eta :=
      L.target_eq
    _ = physicalComponents (rearPeriod S.source)
        G.output.chosen.Delta.eta := by
      rw [H.last_period_eq, H.last_chosen_eta_eq]
    _ = physicalComponents (rearPeriod S.source) G.rawPath.eta := by
      rw [GeometricInput.rawPath, G.output.stage_eq]

end ConcreteAncestry

private theorem configured_sourceKh_pos : 0 < sourceKh := by
  rw [sourceKh_eq]
  norm_num

private theorem configured_rearPeriod_one_le (t : ℝ) :
    1 ≤ rearPeriod S.source t :=
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget.one_le_configured_rearPeriod
    configured_sourceKh_pos t

/-- The fully configured physical row.  The distortion budget, terminal
identity, and rear-period floor are all discharged internally. -/
def physicalRow
    (M : MetricGeometry G)
    (H : ConcreteAncestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G n depth) :
    PhysicalRow S
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      configuredC0 configuredC1 configuredC2
      (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
        edgePhysicalDefect
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
          (n + 1)) :=
  ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow.physicalRow O M H.ancestry
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    H.terminal_eq configured_rearPeriod_one_le

/-- The corresponding theorem-produced physical metric input. -/
def physicalMetric
    (M : MetricGeometry G)
    (H : ConcreteAncestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G n depth) :
    PhysicalMetricInput G
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      configuredC0 configuredC1 configuredC2
      (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
        edgePhysicalDefect
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
          (n + 1)) :=
  (physicalRow O M H).metric

end ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow
