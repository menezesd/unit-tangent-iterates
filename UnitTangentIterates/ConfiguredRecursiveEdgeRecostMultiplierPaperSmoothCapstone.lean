import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperC2Capstone
import UnitTangentIterates.PaperMainTheoremAutomaticSmoothInput

/-!
# Smooth configured multiplier paper capstone

This module canonically reconstructs the limit output and oriented
representatives used by the C2 capstone, then makes the direct branch's sole
additional obligation a rowwise automatic compactness record.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone

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

def directInput (I : PhysicalBaseInput R) : DirectInput R := I.toDirectInput

def geometricScheme (I : PhysicalBaseInput R) :=
  (directInput R I).core.array.toGeometricScheme

def physicalRear (I : PhysicalBaseInput R) :=
  (directInput R I).core.array.physicalRear (directInput R I).core.B0

def terminalScheme (I : PhysicalBaseInput R) :=
  (geometricScheme R I).toScheme (directInput R I).physical.physical
    (directInput R I).kh0_nonnegative (directInput R I).kh0_lt_one
    (directInput R I).cb_pos (directInput R I).db_pos
    (directInput R I).cp_pos (directInput R I).physical.frontTube
    (directInput R I).physical.mixed
    (directInput R I).physical.physicalDefect

/-- Canonical choice of the configured marked limit output. -/
def limitOutput (I : PhysicalBaseInput R) := Nonempty.some
  (TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput_of_distance
    (terminalScheme R I) (directInput R I).c_pos)

theorem physical_tendsto (I : PhysicalBaseInput R) (n : ℕ) :
    Tendsto (physicalRear R I n) atTop (nhds ((limitOutput R I).X n)) :=
  EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
    ((limitOutput R I).row_limit n)
    ((directInput R I).physical.physicalDefect n)

def rowGeometry (I : PhysicalBaseInput R) :=
  geometricRowMarkingDataDirect (directInput R I).physical.markings
    (directInput R I).physical.physical (directInput R I).c_pos
    (geometricScheme R I).tube

def markingBounds (I : PhysicalBaseInput R) := (rowGeometry R I).toRowwiseBounds

def limitReparam (I : PhysicalBaseInput R) (n : ℕ) :
    LimitOrientedReparametrization ((limitOutput R I).X n)
      ((limitOutput R I).X n) :=
  limitOrientedReparametrization_of_rowwise_bounds
    ((markingBounds R I).lambda_pos n)
    ((markingBounds R I).secondBound_nonneg n)
    ((markingBounds R I).reparametrization n) (physical_tendsto R I n)
    ((limitOutput R I).row_limit n) ((markingBounds R I).basepoint n)
    ((markingBounds R I).psi_hasDerivAt n) ((markingBounds R I).ddpsi n)
    ((markingBounds R I).dpsi_hasDerivAt n)
    ((markingBounds R I).ddpsi_bound n)

/-- Canonical oriented arclength representatives from the configured C2
construction. -/
def representatives (I : PhysicalBaseInput R) (n : ℕ) :
    OrientedArclengthRepresentative ((limitOutput R I).X n) := by
  let D := directInput R I
  let W := limitReparam R I n
  have hbase : IsTubeMember D.cb 0 D.db ((limitOutput R I).X n) :=
    (isClosed_tube D.cb 0 D.db).mem_of_tendsto (physical_tendsto R I n)
      (Eventually.of_forall (D.physical.physical.physical_tube n))
  exact orientedArclengthRepresentative_of_orientedReparametrization
    D.cb_pos D.db_pos W.lambda_pos hbase W.reparametrization
    W.psi_hasDerivAt W.dpsi_continuous W.surjective
    (limitStrictnessDataH_of_explicitFrontRowLimit
      D.kh0_nonnegative D.kh0_lt_one D.cb_pos D.cp_pos
      D.physical.physical.physical_tube D.physical.frontTube
      D.physical.mixed (physical_tendsto R I n))

theorem width_gap (I : PhysicalBaseInput R) :
    J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize
        (limitOutput R I) <
      (2 * R.data.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize
        (limitOutput R I)) / Real.pi := by
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize
      (limitOutput R I) = R.radius 0 := by
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

def paperOutput (I : PhysicalBaseInput R) :=
  PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    (limitOutput R I) (representatives R I)
    (directInput R I).baseFacts.direction_norm
    (directInput R I).baseFacts.bounded
    (directInput R I).baseFacts.width
    (directInput R I).baseFacts.length (width_gap R I)

/-- The direct branch's single smoothness obligation: the existing physical
base input plus automatic fixed-row data for the canonical representatives. -/
structure SmoothPhysicalBaseInput (R : RecostClosingOutput J GO) where
  base : PhysicalBaseInput R
  fixedRows : ∀ n,
    PhysicalRearLocalShiftedStageAutomaticClosure.FixedRowInput
      base.kh0 base.cb base.db
      (representatives R base n).q (representatives R base (n + 1)).q

def SmoothPhysicalBaseInput.toAutomaticInput
    (I : SmoothPhysicalBaseInput R) :
    PaperMainTheoremAutomaticSmoothInput.Input
      (limitOutput R I.base) (directInput R I.base).baseFacts.direction
      J.scalar.Cw (R.data.Hs 0) where
  representatives := representatives R I.base
  paperOutput := paperOutput R I.base
  gamma_eq := rfl
  kh := I.base.kh0
  tubeC := I.base.cb
  tubeDlt := I.base.db
  kh_nonneg := I.base.kh0_nonnegative
  kh_lt_one := I.base.kh0_lt_one
  tubeC_pos := I.base.cb_pos
  representative_tube := fun n => (representatives R I.base n).tube
  fixedRows := I.fixedRows

/-- Configured multiplier capstone with explicit C-infinity regularity. -/
theorem paperSmooth (I : SmoothPhysicalBaseInput R) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      InjOn (Gamma 0) (Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  PaperMainTheoremAutomaticSmoothInput.paperSmooth I.toAutomaticInput

end ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone
