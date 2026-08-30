import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawDiagonalBase

/-! # Exact final-tail base layer for intrinsic diagonal nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseLayer

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

/-- The physical base retains the canonical unary stage definitionally.  The
three synchronized scalar fields remain the recursive successor contract. -/
noncomputable def baseNode
    (R : RecostClosingOutput J O) (n : ℕ) : Node where
  P0 := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (rowOutput R n).N 0
  khat := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (rowOutput R n).N 0
  Qmax := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (rowOutput R n).N 0
  stageP0 := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
  stageKhat := fun _ ↦ ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar
  stageQmax := ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax J.scalar
  stageIndex := (rowOutput R n).N
  stage := ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage
    (K0 := K0) (K1 := K1) (K2 := K2) J (rowOutput R n).N

@[simp] theorem baseNode_displayed
    (R : RecostClosingOutput J O) (n : ℕ) :
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) :=
  finalStage_displayed (K0 := K0) (K1 := K1) (K2 := K2) R n

/-- Exact scalar synchronization of the untransported physical base. -/
def baseNode_configured
    (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredNode R n
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n) := by
  refine
    { P0_eq := ?_
      khat_eq := ?_
      Qmax_eq := ?_
      stageP0_at_index_eq := ?_
      stageKhat_at_index_eq := ?_
      stageQmax_at_index_eq := ?_ } <;>
    simp [baseNode,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
      Nat.add_assoc]

private theorem baseNode_source_eq
    (R : RecostClosingOutput J O) (n : ℕ) :
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source =
      (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).asUnary.source := by
  simp [baseNode, baseStage,
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Stage.asUnary,
    ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
    ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
    Nat.add_assoc]

private theorem baseNode_Gamma_eq
    (R : RecostClosingOutput J O) (n : ℕ) :
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.Gamma =
      (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).asUnary.Gamma := by
  simp [baseNode, baseStage,
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Stage.asUnary,
    ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
    ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
    Nat.add_assoc]

private noncomputable def normalizedSourceFacts
    (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedReachableFacts.SourceFacts
      ((finalGaugeOutput R).shiftOutput n)
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source
      (rowP1 R n) 0 := by
  let H := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.state
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  rw [baseNode_source_eq R n]
  simpa [rowP1,
    ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
    Nat.add_assoc] using H.sourceFacts

private noncomputable def normalizedIntrinsic
    (R : RecostClosingOutput J O) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.IntrinsicFrontFunctionalFacts
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source := by
  let H := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.state
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  rw [baseNode_source_eq R n]
  exact H.intrinsic

private theorem normalizedPeriodFloor
    (R : RecostClosingOutput J O) (n : ℕ) (t : ℝ) :
    1 ≤ FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source t := by
  let H := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.state
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  rw [baseNode_source_eq R n]
  exact H.periodFloor t

private theorem exists_normalizedAncestry
    (R : RecostClosingOutput J O) (n : ℕ) :
    ∃ A : ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.ConcreteAncestry
        (RJ := J) (O := (finalGaugeOutput R).shiftOutput n)
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.Gamma
        0 (rowDefect R n),
      A.terminalJ =
          (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.phi1 ∧
        A.terminalP =
          (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.P := by
  let H := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.state
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  refine ⟨H.ancestry, ?_, ?_⟩
  · rw [baseNode_source_eq R n]
    exact H.terminalJ_eq
  · rw [baseNode_source_eq R n]
    exact H.terminalP_eq

/-- The callback-free normalized base state, with no source transport. -/
noncomputable def normalized
    (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State
      ((finalGaugeOutput R).shiftOutput n)
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage
      (rowP1 R n) 0 (rowDefect R n) := by
  let hA := exists_normalizedAncestry (K0 := K0) (K1 := K1) (K2 := K2) R n
  let A := Classical.choose hA
  let hA_spec := Classical.choose_spec hA
  exact
    { sourceFacts := normalizedSourceFacts R n
      intrinsic := normalizedIntrinsic R n
      periodFloor := normalizedPeriodFloor R n
      ancestry := A
      terminalJ_eq := hA_spec.1
      terminalP_eq := hA_spec.2 }

/-- Rear of base row `n` is the displayed physical initial of row `n+1`. -/
theorem baseNode_range
    (R : RecostClosingOutput J O) (n : ℕ) :
    range (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.rear.1 =
      range (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).stage.displayed.1 := by
  change range (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).rear.1 =
    range (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).displayed.1
  simp only [baseStage]
  rw [rowGaugeOutput_N R n, rowGaugeOutput_N R (n + 1)]
  simpa [Nat.add_assoc] using
    (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage_rear_range
      (K0 := K0) (K1 := K1) (K2 := K2) J (R.totalShift + n))

/-- Exact depth-zero reachable layer. -/
noncomputable def layer
    (R : RecostClosingOutput J O) :
    Layer R 0 (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R) where
  configured := baseNode_configured R
  normalized := normalized R

end ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
