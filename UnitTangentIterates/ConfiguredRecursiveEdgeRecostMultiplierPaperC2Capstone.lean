import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
import UnitTangentIterates.PaperMainTheoremC2Projection

/-!
# C2 paper capstone for multiplier-aware direct recost rows

This leaf retains the oriented arclength representatives that the legacy
paper projection forgets.  It therefore exposes the `C2` regularity of every
curve and ties the displayed physical period to injectivity on one period.
No existing capstone API is changed.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostMultiplierPaperC2Capstone

open ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgePhysicalInitialData
  ConfiguredRecursiveEdgePhysicalInitialWidth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray
  GenericVariableTerminalDirectCapstoneExplicitFront
  GaugeRearFamilyVariableTerminal
  RichFamilyPhysicalMarkingIntegration

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {GO : GaugeOutput J} (R : RecostClosingOutput J GO)

/-- The final configured paper theorem with the regularity and simple-period
facts retained by the ordinary physical representatives. -/
theorem paperC2 (I : PhysicalBaseInput R) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      InjOn (Gamma 0) (Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (2 : ℕ) (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let D := I.toDirectInput
  let G := D.core.array.toGeometricScheme
  let B := D.core.array.physicalRear D.core.B0
  let S := G.toScheme D.physical.physical
    D.kh0_nonnegative D.kh0_lt_one D.cb_pos D.db_pos D.cp_pos
    D.physical.frontTube D.physical.mixed D.physical.physicalDefect
  obtain ⟨O⟩ :=
    TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput_of_distance
      S D.c_pos
  have hphysical : ∀ n, Tendsto (B n) atTop (nhds (O.X n)) := fun n =>
    EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (D.physical.physicalDefect n)
  let rowGeometry := geometricRowMarkingDataDirect
    D.physical.markings D.physical.physical D.c_pos G.tube
  let markingBounds := rowGeometry.toRowwiseBounds
  let limitReparam : ∀ n x, Tendsto (D.core.P n) atTop (nhds x) →
      LimitOrientedReparametrization (O.X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (hphysical n) hx
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
  let reps : ∀ n, OrientedArclengthRepresentative (O.X n) := by
    intro n
    let W := limitReparam n (O.X n) (O.row_limit n)
    have hbase : IsTubeMember D.cb 0 D.db (O.X n) :=
      (isClosed_tube D.cb 0 D.db).mem_of_tendsto (hphysical n)
        (Eventually.of_forall (D.physical.physical.physical_tube n))
    exact orientedArclengthRepresentative_of_orientedReparametrization
      D.cb_pos D.db_pos W.lambda_pos hbase W.reparametrization
      W.psi_hasDerivAt W.dpsi_continuous W.surjective
      (limitStrictnessDataH_of_explicitFrontRowLimit
        D.kh0_nonnegative D.kh0_lt_one D.cb_pos D.cp_pos
        D.physical.physical.physical_tube D.physical.frontTube
        D.physical.mixed (hphysical n))
  have hgap :
      J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * R.data.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize O) /
          Real.pi := by
    have hshadow :
        PaperFacingVariableTerminalOutput.shadowSize O = R.radius 0 := by
      simp [PaperFacingVariableTerminalOutput.shadowSize,
        ActualStageProvider.paper_rowC,
        ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.error,
        ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.radius,
        ExponentialDiagonalLargeSeparation.rowRadius,
        ExponentialDiagonalLargeSeparation.rowError,
        ShadowingTails.tail,
        ExponentialDiagonalLargeSeparation.shiftSequence,
        Nat.add_assoc]
    rw [hshadow]
    exact R.width_gap
  let A := PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O reps D.baseFacts.direction_norm D.baseFacts.bounded D.baseFacts.width
      D.baseFacts.length hgap
  apply PaperMainTheoremC2Projection.of_output_of_representatives reps A
  rfl

end ConfiguredRecursiveEdgeRecostMultiplierPaperC2Capstone
