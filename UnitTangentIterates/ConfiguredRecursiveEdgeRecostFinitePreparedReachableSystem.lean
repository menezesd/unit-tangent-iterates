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
  coherentPhase : ℕ → ℝ
  coherentDistance : ∀ n,
    dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
        (MarkedShift.shiftData (coherentPhase n) (nodes n).stage.displayed) ≤
      ∑ j ∈ Finset.range k, H.error n j
  layer : Layer (budget H) (stateP1 H) (defect H) k nodes
  presented : ∀ n, PresentedInput (nodes n).stage
  selection : ∀ n, SelectionBounds (nodes n).stage.source

namespace PreparedReachable

noncomputable def pre {k : ℕ} (Z : PreparedReachable H k) (n : ℕ) :
    Core (Z.nodes n).stage := (Z.presented n).core

/-- A depth-zero family whose displayed rows are the configured base rows is
coherent with phase zero.  Keeping this generic prevents concrete base-layer
definitions from generating a very large reduction proof. -/
theorem coherentDistance_zero_of_displayed_eq
    (nodes : ℕ → Node)
    (hdisplayed : ∀ n, (nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
    (n : ℕ) :
    dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
        (MarkedShift.shiftData 0 (nodes n).stage.displayed) ≤
      ∑ j ∈ Finset.range 0, H.error n j := by
  rw [hdisplayed n]
  simp only [MarkedShift.shiftData_zero, dist_self, Finset.range_zero,
    Finset.sum_empty, le_refl]

/-- Package a depth-zero prepared system without exposing its concrete
dependent records to the kernel while it checks the constructor literal. -/
noncomputable def zero
    (nodes : ℕ → Node)
    (hdisplayed : ∀ n, (nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
    (layer : Layer (budget H) (stateP1 H) (defect H) 0 nodes)
    (presented : ∀ n, PresentedInput (nodes n).stage)
    (selection : ∀ n, SelectionBounds (nodes n).stage.source) :
    PreparedReachable H 0 where
  nodes := nodes
  coherentPhase := fun _ ↦ 0
  coherentDistance := coherentDistance_zero_of_displayed_eq H nodes hdisplayed
  layer := layer
  presented := presented
  selection := selection

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
  mappedRearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (input.analytic n).source t s| ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
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

theorem coherentDistance_step
    (I : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
      J H (budget H) Z.layer)
    (phase : ℕ → ℝ)
    (hphase : ∀ n, I.nextDisplayed n =
      MarkedShift.shiftData (phase n) (I.pre n).geometric.base)
    (n : ℕ) :
    dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
        (MarkedShift.shiftData (Z.coherentPhase n - phase n)
          (I.nextDisplayed n)) ≤
      ∑ j ∈ Finset.range (k + 1), H.error n j := by
  have hshift :
      MarkedShift.shiftData (Z.coherentPhase n - phase n)
          (I.nextDisplayed n) =
        MarkedShift.shiftData (Z.coherentPhase n)
          (I.pre n).geometric.base := by
    rw [hphase n, MarkedShift.shiftData_add]
    congr 1
    ring
  rw [hshift, Finset.sum_range_succ]
  refine (dist_triangle _
    (MarkedShift.shiftData (Z.coherentPhase n) (Z.nodes n).stage.displayed) _).trans ?_
  refine add_le_add (Z.coherentDistance n) ?_
  rw [FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.dist_shiftData]
  exact (I.rawMetric n).dist_displayed_base_le.trans
    (I.edgeBudget_le_error n)

theorem coherentDistance_next (I : PreparedStepData H Z) (n : ℕ) :
    dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
        (MarkedShift.shiftData (Z.coherentPhase n - I.initialPhase n)
          (I.input.nextDisplayed n)) ≤
      ∑ j ∈ Finset.range (k + 1), H.error n j :=
  coherentDistance_step H I.input I.initialPhase
    I.nextDisplayed_eq_phase n

noncomputable def next (I : PreparedStepData H Z) :
    PreparedReachable H (k + 1) where
  nodes := I.input.step.next
  coherentPhase := fun n ↦ Z.coherentPhase n - I.initialPhase n
  coherentDistance := by
    intro n
    change dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
        (MarkedShift.shiftData (Z.coherentPhase n - I.initialPhase n)
          (I.input.nextDisplayed n)) ≤ _
    exact I.coherentDistance_next H n
  layer := I.input.nextLayer
  presented := fun n ↦ (I.boundaryFacts H n).presentedInput
  selection := fun n ↦ (I.recursiveFacts n).sidecars.selection

end PreparedStepData

end ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
