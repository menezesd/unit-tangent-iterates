import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialWidth

/-! # Final paper capstone for multiplier-aware direct recost rows -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone

open ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgePhysicalInitialData
  ConfiguredRecursiveEdgePhysicalInitialWidth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

/-- Geometric array data whose step metric is charged only to the final
multiplier-aware error. -/
structure GeometricCore where
  Q : ℕ → Data
  P : ℕ → ℕ → Data
  B0 : ℕ → Data
  C : ℕ → ℝ
  c : ℝ
  dlt : ℝ
  cell : ∀ n k, Cell P n k
  base : ∀ n, P n 0 = Q n
  tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepDistance : ∀ n k, dist (P n k) (P n (k + 1)) ≤ R.error n k

namespace GeometricCore

/-- Actual presented array with scalar bookkeeping coefficient one. -/
def array (G : GeometricCore R) :
    Array G.Q G.P R.error
      ActualStageProvider.paperP0 ActualStageProvider.paperP1
      ActualStageProvider.paperKhat ActualStageProvider.paperG1
      ActualStageProvider.paperCg G.C G.c G.dlt where
  cell := G.cell
  base := G.base
  error_nonnegative := R.error_nonnegative
  error_summable := R.error_summable
  tube := G.tube
  stepDistance := by
    intro n k
    simpa [ActualStageProvider.paper_rowC] using G.stepDistance n k

end GeometricCore

/-- Parameterization-invariant facts about the truthful physical initial row
at the final total shift. -/
structure BaseFacts (G : GeometricCore R) where
  direction : ℂ
  direction_norm : ‖direction‖ = 1
  bounded : Bornology.IsBounded (range (⇑(G.Q 0).1))
  width : Width.width (range (⇑(G.Q 0).1)) direction ≤ J.scalar.Cw
  length : 2 * R.data.Hs 0 ≤
    MarkedReparam.totalLength (fun u ↦ (G.Q 0).2.1 u)

namespace BaseFacts

/-- The truthful selected physical rear at the final multiplier closing shift
supplies every base sidecar.  In particular, its width is obtained from the
selected-rear stability theorem, not from an identification with the model
front. -/
def ofPhysicalInitial
    (G : GeometricCore R)
    (hPzero : ∀ n, G.P n 0 =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n)) :
    BaseFacts R G := by
  let N := R.totalShift
  have hp := ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar N
  have hbounded : Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial
        J.scalar N).1)) :=
    CurveDistance.isBounded_range_of_periodic
      (continuous_iff_continuousAt.2 fun u ↦
        (hp.hasDerivAt_curve u).continuousAt)
      hp.periodic one_pos
  refine
    { direction := initialDirection J.scalar N
      direction_norm := initialDirection_norm J.scalar N
      bounded := ?_
      width := ?_
      length := ?_ }
  · rw [← G.base 0, hPzero 0]
    simpa [N] using hbounded
  · rw [← G.base 0, hPzero 0]
    simpa [N] using initial_width_le_Cw J.scalar N hbounded
  · rw [← G.base 0, hPzero 0]
    change 2 * R.data.Hs 0 ≤
      MarkedReparam.totalLength (fun u ↦
        (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar N).2.1 u)
    rw [
      VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube hp,
      ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq J.scalar N]
    simp [N, RecostClosingOutput.data_eq_shift_capstoneData,
      ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredBaseProfiledEdgeSourceFamily.data,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc]

end BaseFacts

/-- Minimal final input.  Reachable rows fill `core`; physical-initial
sidecars fill `baseFacts`; no scalar callback remains. -/
structure DirectInput where
  core : GeometricCore R
  kh0 : ℝ
  cb : ℝ
  db : ℝ
  cp : ℝ
  dp : ℝ
  physical : Package core.array core.B0 kh0 cb db cp dp
  kh0_nonnegative : 0 ≤ kh0
  kh0_lt_one : kh0 < 1
  cb_pos : 0 < cb
  db_pos : 0 < db
  cp_pos : 0 < cp
  c_pos : 0 < core.c
  baseFacts : BaseFacts R core

/-- Final input whose depth-zero row is the actual configured physical rear.
Unlike `DirectInput`, it has no abstract base-geometry callback. -/
structure PhysicalBaseInput where
  core : GeometricCore R
  kh0 : ℝ
  cb : ℝ
  db : ℝ
  cp : ℝ
  dp : ℝ
  physical : Package core.array core.B0 kh0 cb db cp dp
  kh0_nonnegative : 0 ≤ kh0
  kh0_lt_one : kh0 < 1
  cb_pos : 0 < cb
  db_pos : 0 < db
  cp_pos : 0 < cp
  c_pos : 0 < core.c
  P_zero : ∀ n, core.P n 0 =
    ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
      (R.totalShift + n)

namespace DirectInput

private theorem universal_gap (I : DirectInput R) :
    ∀ Z : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      I.core.Q I.core.P R.error
      ActualStageProvider.paperP0 ActualStageProvider.paperP1
      ActualStageProvider.paperKhat ActualStageProvider.paperG1
      ActualStageProvider.paperCg I.core.C I.core.c I.core.dlt,
      J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize Z <
        (2 * R.data.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize Z) /
          Real.pi := by
  intro Z
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize Z = R.radius 0 := by
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

/-- Final paper theorem with all multiplier scalar tails discharged by `R`. -/
theorem paper (I : DirectInput R) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  apply GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain.paperMainDistance
    I.core.array.toGeometricScheme I.physical.markings I.physical.physical
    I.kh0_nonnegative I.kh0_lt_one I.cb_pos I.db_pos I.cp_pos
    I.physical.frontTube I.physical.mixed I.physical.physicalDefect I.c_pos
    (direction := I.baseFacts.direction)
    (modelWidth := J.scalar.Cw)
    (H := R.data.Hs 0)
  · exact I.baseFacts.direction_norm
  · exact I.baseFacts.bounded
  · exact I.baseFacts.width
  · exact I.baseFacts.length
  · exact I.universal_gap

end DirectInput

namespace PhysicalBaseInput

/-- Insert the canonical truthful physical-base facts. -/
def toDirectInput (I : PhysicalBaseInput R) : DirectInput R where
  core := I.core
  kh0 := I.kh0
  cb := I.cb
  db := I.db
  cp := I.cp
  dp := I.dp
  physical := I.physical
  kh0_nonnegative := I.kh0_nonnegative
  kh0_lt_one := I.kh0_lt_one
  cb_pos := I.cb_pos
  db_pos := I.db_pos
  cp_pos := I.cp_pos
  c_pos := I.c_pos
  baseFacts := BaseFacts.ofPhysicalInitial R I.core I.P_zero

/-- Final paper theorem from the multiplier closing output and the truthful
configured physical base row. -/
theorem paper_of_physicalBase (I : PhysicalBaseInput R) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  I.toDirectInput.paper

end PhysicalBaseInput

end ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
