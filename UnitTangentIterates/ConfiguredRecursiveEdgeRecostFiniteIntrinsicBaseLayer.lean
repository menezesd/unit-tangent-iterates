import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness

/-! # Physical base layer over the finite diagonal history budget -/

set_option maxHeartbeats 4000000

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer

open ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeWeightedBaseGaugeHistoryMajor
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorHistory
  FiniteNonaffineMajorLayer
  FiniteNonaffineMajorNormalizedState

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {K0 K1 K2 : ℝ}

/-- Every row on diagonal `q` uses the full length-`q` segment budget. -/
noncomputable def budget (H : Output R) (q : ℕ) :
    MajorBudget ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal :=
  H.historyBudget q q (Nat.le_refl q)

@[simp] theorem budget_major_of_le (H : Output R) (q j : ℕ) (hj : j ≤ q) :
    (budget H q).major j = H.epsDiag q := by
  exact H.historyBudget_major_of_le q q j (Nat.le_refl q) hj

/-- At depth zero an old concrete ancestry contains no links, so its endpoint
and component data can be installed over any truthful explicit major budget. -/
noncomputable def ancestryOfDepthZero
    {p q : Data} {Gamma : NormalPath p q} {edgeDefect : ℝ}
    {Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {Og : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      RJ Etotal Dtarget}
    (B : MajorBudget Etotal)
    (A : ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.ConcreteAncestry
      (O := Og) Gamma 0 edgeDefect) :
    FiniteNonaffineMajorHistory.ConcreteAncestry B Gamma 0 edgeDefect where
  ancestry :=
    { V := A.ancestry.V
      baseJ := A.ancestry.baseJ
      baseP := A.ancestry.baseP
      baseEta := A.ancestry.baseEta
      base_eq := A.ancestry.base_eq
      d_nonnegative := A.ancestry.d_nonnegative
      components_nonnegative := A.ancestry.components_nonnegative
      initial_le := A.ancestry.initial_le
      links := by intro j hj; omega }
  terminalJ := A.terminalJ
  terminalP := A.terminalP
  terminal_eq := A.terminal_eq

/-- The lightweight canonical nodes on the final history closing. -/
abbrev nodes (H : Output R) :=
  baseNode (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing

/-- The already-proved physical state is kept opaque while its facts are
recharged to the explicit finite major. -/
noncomputable def legacyState (H : Output R) (n : ℕ) :=
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.normalized
    (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n

/-- The physical base source facts charged to the unified diagonal epsilon. -/
noncomputable def sourceFacts (H : Output R) (n : ℕ) :
    FiniteNonaffineMajorNormalizedState.SourceFacts (budget H n)
      (nodes (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source
      (stateP1 H n) 0 := by
  let A := legacyState (K0 := K0) (K1 := K1) (K2 := K2) H n
  have hepsBase : A.sourceFacts.eps ≤
      combinedGaugeMajor H.data J.scalar.Mend
        (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredSourceMassTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2) n := by
    have hbase := A.sourceFacts.eps_le_major
    rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.shiftOutput_major]
      at hbase
    simp only [Nat.add_zero] at hbase
    rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.major,
      ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data,
      H.toClosing_data] at hbase
    exact hbase
  have heps : A.sourceFacts.eps ≤ (budget H n).major 0 := by
    rw [budget_major_of_le H n 0 (Nat.zero_le n)]
    exact hepsBase.trans (H.baseGaugeMajor_le_epsDiag n)
  refine
    { slice := A.sourceFacts.slice
      periodUpper_le := ?_
      functional := A.sourceFacts.functional
      eps := A.sourceFacts.eps
      jets := A.sourceFacts.jets
      eps_le_major := heps }
  simpa [A, legacyState, nodes, stateP1,
    ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer.rowP1,
    ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput] using
    A.sourceFacts.periodUpper_le

/-- Depth-zero endpoint ancestry over the same explicit budget. -/
noncomputable def baseAncestry (H : Output R) (n : ℕ) :
    FiniteNonaffineMajorHistory.ConcreteAncestry (budget H n)
      (nodes (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.Gamma
      0 (defect H n) := by
  let A := legacyState (K0 := K0) (K1 := K1) (K2 := K2) H n
  simpa [A, legacyState, nodes, defect,
    ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer.rowDefect,
    ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput] using
      (ancestryOfDepthZero (budget H n) A.ancestry)

/-- The finite-major state type at one physical base row. -/
abbrev StateAt (H : Output R) (n : ℕ) :=
  FiniteNonaffineMajorNormalizedState.State (budget H n)
    (S := (nodes (K0 := K0) (K1 := K1) (K2 := K2) H n).stage)
    (P1 := stateP1 H n)
    (depth := 0) (edgeDefect := defect H n)

/-- The physical base state charged to the unified base-plus-recost history
epsilon at its public row index. -/
noncomputable def normalized (H : Output R) (n : ℕ) : StateAt H n := by
  let A := legacyState (K0 := K0) (K1 := K1) (K2 := K2) H n
  refine
    { sourceFacts := sourceFacts (K0 := K0) (K1 := K1) (K2 := K2) H n
      intrinsic := A.intrinsic
      periodFloor := A.periodFloor
      ancestry := baseAncestry (K0 := K0) (K1 := K1) (K2 := K2) H n
      terminalJ_eq := ?_
      terminalP_eq := ?_ }
  · simpa [baseAncestry, A, legacyState] using A.terminalJ_eq
  · simpa [baseAncestry, A, legacyState] using A.terminalP_eq

/-- Callback-free finite-major depth-zero layer on the final history tail. -/
noncomputable def layer (H : Output R) :
    FiniteNonaffineMajorLayer.Layer (budget H) (stateP1 H) (defect H) 0
      (nodes (K0 := K0) (K1 := K1) (K2 := K2) H) where
  normalized n := by
    simpa using (normalized (K0 := K0) (K1 := K1) (K2 := K2) H n)

end ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
