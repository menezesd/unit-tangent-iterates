import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
import UnitTangentIterates.CoherentPhaseReachableMetricRange

/-! # Prepared reachable finite-major multiplier system -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorLayer
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- Full finite segment budget on the invariant diagonal. -/
noncomputable def budget (q : ℕ) : MajorBudget
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal :=
  H.historyBudget q q (Nat.le_refl q)

@[simp] theorem budget_major_of_le (q j : ℕ) (hj : j ≤ q) :
    (budget H q).major j = H.epsDiag q :=
  H.historyBudget_major_of_le q q j (Nat.le_refl q) hj

/-- A reached finite-major layer with the native presented boundary and the
fresh source-tied selection bounds needed at the next step. -/
structure PreparedReachable (k : ℕ) where
  nodes : ℕ → Node
  layer : Layer (budget H) (stateP1 H) (defect H) k nodes
  presented : ∀ n, PresentedInput (nodes n).stage
  selection : ∀ n, SelectionBounds (nodes n).stage.source

namespace PreparedReachable

noncomputable def pre {k : ℕ} (Z : PreparedReachable H k) (n : ℕ) :
    Core (Z.nodes n).stage := (Z.presented n).core

end PreparedReachable

/-- A complete theorem-produced step.  The finite normalized successor and
the next native presented inputs are reconstructed from the same analytic
sources; no independent terminal choice remains. -/
structure PreparedStepData {k : ℕ} (Z : PreparedReachable H k) where
  input : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
    J H (budget H) Z.layer
  pre_eq : ∀ n, input.pre n = Z.pre H n
  recursiveFacts : ∀ n, Input.RecursiveFacts (input.analytic n)
  nextDisplayed_eq_selected : ∀ n,
    input.nextDisplayed n = (input.analytic n).source.selectedRearData 0
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(input.pre (n + 1)).path.T,
      (input.analytic n).source.m t) ≤ H.error n (k + 1)
  initialPhase : ℕ → ℝ
  nextDisplayed_eq_phase : ∀ n,
    input.nextDisplayed n = MarkedShift.shiftData (initialPhase n)
      (input.pre n).geometric.base
  rawDiagonalRangeEdge : ∀ n,
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (Z.nodes (n + 1)).stage.displayed (input.pre n).geometric.base
  terminalReference_eq : ∀ n,
    input.terminalFrontReference n = input.nextDisplayed (n + 1)

namespace PreparedStepData

variable {k : ℕ} {Z : PreparedReachable H k}

def boundaryFacts (I : PreparedStepData H Z) (n : ℕ) :
    BoundaryFacts I.input n (H.error n (k + 1)) where
  recursiveFacts := I.recursiveFacts n
  displayed_eq := I.nextDisplayed_eq_selected n
  cost_le := I.mappedCost_le n

noncomputable def next (I : PreparedStepData H Z) :
    PreparedReachable H (k + 1) where
  nodes := I.input.step.next
  layer := I.input.nextLayer
  presented := fun n ↦ (I.boundaryFacts H n).presentedInput
  selection := fun n ↦ (I.recursiveFacts n).sidecars.selection

end PreparedStepData

structure Provider where
  base : PreparedReachable H 0
  baseDisplayed : ∀ n,
    (base.nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n
  step : ∀ k (Z : PreparedReachable H k), Nonempty (PreparedStepData H Z)

namespace Provider

variable (P : Provider H)

noncomputable def reachable : ∀ k, PreparedReachable H k
  | 0 => P.base
  | k + 1 =>
      let Z := reachable k
      (Classical.choice (P.step k Z)).next H

noncomputable def stepData (k : ℕ) : PreparedStepData H (P.reachable H k) :=
  Classical.choice (P.step k (P.reachable H k))

@[simp] theorem reachable_succ_nodes (k : ℕ) :
    (P.reachable H (k + 1)).nodes = (P.stepData H k).input.step.next := by
  simp [reachable, stepData, PreparedStepData.next]

def raw (n k : ℕ) : Data := ((P.reachable H k).nodes n).stage.displayed
def canonical (n k : ℕ) : Data := ((P.stepData H k).input.pre n).geometric.base
def terminalReference (n k : ℕ) : Data :=
  (P.stepData H k).input.terminalFrontReference n

noncomputable def coherence (k : ℕ) :
    StepCoherence (fun n ↦ P.raw H n k) (fun n ↦ P.raw H n (k + 1))
      (P.canonical H · k) (P.terminalReference H · k) where
  initialPhase := (P.stepData H k).initialPhase
  nextDisplayed_eq_phase n := by
    simpa [raw, canonical, reachable_succ_nodes] using
      (P.stepData H k).nextDisplayed_eq_phase n
  rawDiagonalRangeEdge n := (P.stepData H k).rawDiagonalRangeEdge n
  terminalReference_eq n := by
    simpa [raw, terminalReference, reachable_succ_nodes] using
      (P.stepData H k).terminalReference_eq n

theorem rawDistance (n k : ℕ) :
    dist (P.raw H n k) (P.canonical H n k) ≤ H.error n k := by
  exact ((P.stepData H k).input.rawMetric n).dist_displayed_base_le.trans
    ((P.stepData H k).input.edgeBudget_le_error n)

noncomputable def system :
    System (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing)
      H.error where
  raw := P.raw H
  canonical := P.canonical H
  terminalReference := P.terminalReference H
  base_eq n := by
    simpa [raw, reachable] using P.baseDisplayed n
  coherence := P.coherence H
  rawDistance := P.rawDistance H

end Provider

end ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
