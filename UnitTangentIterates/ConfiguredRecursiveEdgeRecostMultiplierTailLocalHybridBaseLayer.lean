import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseNormalizedState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment

/-! # Fresh intrinsic base layer on the tail-local hybrid state -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseLayer

open ConfiguredRecursiveEdgePhysicalBaseNormalizedState
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

abbrev node (R : RecostClosingOutput J O) :=
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node
    (K0 := K0) (K1 := K1) (K2 := K2) R

def configured (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredNode R n
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n) :=
  { P0_eq := (ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node_scalars
      (K0 := K0) (K1 := K1) (K2 := K2) R n).1.trans
      (ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.baseNode_configured R n).P0_eq
    khat_eq := (ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node_scalars
      (K0 := K0) (K1 := K1) (K2 := K2) R n).2.1.trans
      (ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.baseNode_configured R n).khat_eq
    Qmax_eq := (ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment.node_scalars
      (K0 := K0) (K1 := K1) (K2 := K2) R n).2.2.trans
      (ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.baseNode_configured R n).Qmax_eq }

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

/-- The native source is the same dependent source as the truthful physical
base source; only its scalar-profile packaging differs. -/
theorem node_source_heq_raw (R : RecostClosingOutput J O) (n : ℕ) :
    HEq (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J (R.totalShift + n)).source := by
  rfl

theorem node_Gamma_heq_raw (R : RecostClosingOutput J O) (n : ℕ) :
    HEq (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.Gamma
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J (R.totalShift + n)).Gamma := by
  rfl

/-- Existing normalized source/jet facts, re-elaborated on the exact hybrid
source rather than transported as a complete normalized state. -/
noncomputable def sourceFacts (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedReachableFacts.SourceFacts
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput n)
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source
      (rowP1 R n) 0 := by
  have hs := node_source_heq_raw (K0 := K0) (K1 := K1) (K2 := K2) R n
  cases hs
  let F := ConfiguredRecursiveEdgePhysicalBaseNormalizedState.sourceFacts
      (K0 := K0) (K1 := K1) (K2 := K2)
      (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R)
      target_nonnegative n
  dsimp only at F
  rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.shiftOutput_N,
    ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_N] at F
  simpa [rowP1, Nat.add_assoc] using F

/-- Intrinsic-front integrability is also reconstructed on the same exact
physical source. -/
noncomputable def intrinsic (R : RecostClosingOutput J O) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.IntrinsicFrontFunctionalFacts
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source := by
  have hs := node_source_heq_raw (K0 := K0) (K1 := K1) (K2 := K2) R n
  cases hs
  exact
    ConfiguredRecursiveEdgePhysicalBaseIntrinsicFunctional.stageIntrinsicFrontFunctionalFacts
      (K0 := K0) (K1 := K1) (K2 := K2) J (R.totalShift + n)

theorem periodFloor (R : RecostClosingOutput J O) (n : ℕ) (t : ℝ) :
    1 ≤ FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source t :=
  ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod t

end ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBaseLayer
