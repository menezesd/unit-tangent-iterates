import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema

/-! # Chosen prepared reachable chain

This packages one actual prepared successor at every depth.  Unlike the
older provider interface, it does not require a step from every possible
reachable state.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteNonaffineMajorLayer

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- One coherent, chosen sequence of prepared reachable layers and the
theorem-produced step used at each depth. -/
structure ChosenChain where
  reachable : ∀ k, PreparedReachable H k
  stepData : ∀ k, PreparedStepData H (reachable k)
  geometry : ∀ k, PreparedGeometryProvenance H k (reachable k)
  baseDisplayed : ∀ n,
    ((reachable 0).nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n
  successorReachable : ∀ k,
    reachable (k + 1) = (stepData k).next H

namespace ChosenChain

variable (C : ChosenChain H)

@[simp] theorem reachable_succ_nodes (k : ℕ) :
    (C.reachable (k + 1)).nodes = (C.stepData k).input.step.next := by
  simpa [PreparedStepData.next] using congrArg
    (fun Z : PreparedReachable H (k + 1) ↦ Z.nodes)
    (C.successorReachable k)

def raw (n k : ℕ) : Data := ((C.reachable k).nodes n).stage.displayed

def canonical (n k : ℕ) : Data :=
  ((C.stepData k).input.pre n).geometric.base

def terminalReference (n k : ℕ) : Data :=
  (C.stepData k).input.terminalFrontReference n

noncomputable def coherence (k : ℕ) :
    StepCoherence (fun n ↦ raw H C n k) (fun n ↦ raw H C n (k + 1))
      (fun n ↦ canonical H C n k) (fun n ↦ terminalReference H C n k) where
  initialPhase := (C.stepData k).initialPhase
  nextDisplayed_eq_phase n := by
    change ((C.reachable (k + 1)).nodes n).stage.displayed =
      MarkedShift.shiftData ((C.stepData k).initialPhase n)
        ((C.stepData k).input.pre n).geometric.base
    rw [reachable_succ_nodes H C k]
    simpa [PreparedStepData.next] using
      (C.stepData k).nextDisplayed_eq_phase n
  rawDiagonalRangeEdge n := (C.stepData k).rawDiagonalRangeEdge n
  terminalReference_eq n := by
    change (C.stepData k).input.terminalFrontReference n =
      ((C.reachable (k + 1)).nodes (n + 1)).stage.displayed
    rw [reachable_succ_nodes H C k]
    simpa [PreparedStepData.next] using
      (C.stepData k).terminalReference_eq n

theorem rawDistance (n k : ℕ) :
    dist (raw H C n k) (canonical H C n k) ≤ H.error n k := by
  exact ((C.stepData k).input.rawMetric n).dist_displayed_base_le.trans
    ((C.stepData k).input.edgeBudget_le_error n)

noncomputable def system :
    System (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing)
      H.error where
  raw := raw H C
  canonical := canonical H C
  terminalReference := terminalReference H C
  base_eq n := by
    simpa [raw] using C.baseDisplayed n
  coherence := coherence H C
  rawDistance := rawDistance H C

end ChosenChain

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
