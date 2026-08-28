import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseNormalizedState

/-!
# Native normalized base layer on the tail-local hybrid column

The base normalized certificate is rebuilt on the intrinsic node itself.
Only the already proved scalar/path formulas of the physical base are used;
no equality or `HEq` between complete dependent state records is required.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseNormalizedLayer

open ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  ConfiguredRecursiveEdgePhysicalBaseNormalizedState
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseLayer
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

private theorem target_nonnegative :
    0 ≤ ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredSourceMassTarget
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 :=
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredSourceMassTarget_nonnegative
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2

/-- Fresh configured ancestry at depth zero on the native tail-local path. -/
noncomputable def ancestry (R : RecostClosingOutput J O) (n : ℕ) :
    ConcreteAncestry
      (O := (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput n)
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.Gamma 0
      (rowDefect R n) := by
  let H := ConfiguredRecursiveEdgePhysicalBaseNormalizedState.baseState
    (K0 := K0) (K1 := K1) (K2 := K2)
    (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R)
    target_nonnegative
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth n
  dsimp only at H
  rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.shiftOutput_N,
    ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_N] at H
  refine
    { ancestry := ?_
      terminalJ :=
        (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.phi1
      terminalP :=
        (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.P
      terminal_eq := ?_ }
  · simpa [rowDefect,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
      ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
      ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_N,
      compositionBaseCorrelated_path, Nat.add_assoc] using H.ancestry.ancestry
  · have hterminal := H.ancestry.terminal_eq
    rw [H.terminalJ_eq, H.terminalP_eq] at hterminal
    simpa [
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
      ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
      ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_N,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      Nat.add_assoc] using hterminal

@[simp] theorem ancestry_terminalJ (R : RecostClosingOutput J O) (n : ℕ) :
    (ancestry (K0 := K0) (K1 := K1) (K2 := K2) R n).terminalJ =
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.phi1 := by
  rfl

@[simp] theorem ancestry_terminalP (R : RecostClosingOutput J O) (n : ℕ) :
    (ancestry (K0 := K0) (K1 := K1) (K2 := K2) R n).terminalP =
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.P := by
  rfl

/-- Fresh normalized state on the native tail-local node. -/
noncomputable def normalized (R : RecostClosingOutput J O) (n : ℕ) :
    State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput n)
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage
      (rowP1 R n) 0 (rowDefect R n) where
  sourceFacts := sourceFacts R n
  intrinsic := intrinsic R n
  periodFloor := periodFloor R n
  ancestry := ancestry R n
  terminalJ_eq := ancestry_terminalJ R n
  terminalP_eq := ancestry_terminalP R n

/-- Callback-free intrinsic normalized layer at tail-local depth zero. -/
noncomputable def layer (R : RecostClosingOutput J O) :
    Layer R 0 (node (K0 := K0) (K1 := K1) (K2 := K2) R) where
  configured := configured R
  normalized := normalized R

end ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseNormalizedLayer
