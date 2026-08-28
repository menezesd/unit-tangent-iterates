import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPresentedReadiness
import UnitTangentIterates.CoherentPhaseReachableMetricRange

/-! # Prepared reachable-only intrinsic multiplier system -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedReachableSystem

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicCoherentReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPresentedReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedPreCarrier
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

/-- A reached layer together with the exact native cores that produced it. -/
structure PreparedReachable (k : ℕ) where
  nodes : ℕ → Node
  layer : Layer R k nodes
  presented : ∀ n, PresentedInput (nodes n).stage
  selection : ∀ n, SelectionBounds (nodes n).stage.source

namespace PreparedReachable

/-- The current native core is not independent data: it is the core of the
retained theorem-produced presented terminal input. -/
noncomputable def pre {k : ℕ} (Z : PreparedReachable R k) (n : ℕ) :
    Core (Z.nodes n).stage :=
  (Z.presented n).core

end PreparedReachable

/-- One coherent step tied to the retained current cores.  Presented
readiness constructs the next cores; no terminal or core callback remains. -/
structure PreparedStepData {k : ℕ} (Z : PreparedReachable R k) where
  coherent : CoherentReadiness R Z.layer
  pre_eq : ∀ n, coherent.pre n = PreparedReachable.pre R Z n
  presented : PresentedReadiness R coherent

namespace PreparedStepData

variable {k : ℕ} {Z : PreparedReachable R k}

noncomputable def phaseStep (I : PreparedStepData R Z) :
    ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem.StepData
      R ⟨Z.nodes, Z.layer⟩ :=
  I.coherent.stepData R

noncomputable def next (I : PreparedStepData R Z) :
    PreparedReachable R (k + 1) where
  nodes := ((I.coherent.inputData R).step).next
  layer := (I.coherent.inputData R).nextLayer
  presented := I.presented.presentedInput R
  selection := fun n => (I.presented.recursiveFacts n).sidecars.selection

end PreparedStepData

/-- The base is explicit because its native ancestry is a separate physical
certificate.  Successors are requested only for actually reached prepared
layers. -/
structure Provider where
  base : PreparedReachable R 0
  base_displayed : ∀ n,
    (base.nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R n
  step : ∀ k (Z : PreparedReachable R k), Nonempty (PreparedStepData R Z)

namespace Provider

variable (H : Provider R)

noncomputable def reachable : ∀ k, PreparedReachable R k
  | 0 => H.base
  | k + 1 =>
      let Z := reachable k
      (Classical.choice (H.step k Z)).next R

noncomputable def stepData (k : ℕ) :
    PreparedStepData R (reachable R H k) :=
  Classical.choice (H.step k (reachable R H k))

@[simp] theorem reachable_succ_nodes (k : ℕ) :
    (reachable R H (k + 1)).nodes =
      ((((stepData R H k).coherent.inputData R).step).next) := by
  simp [reachable, stepData, PreparedStepData.next]

def raw (n k : ℕ) : Data :=
  ((reachable R H k).nodes n).stage.displayed

def canonical (n k : ℕ) : Data :=
  (((stepData R H k).coherent.inputData R).pre n).geometric.base

def terminalReference (n k : ℕ) : Data :=
  ((stepData R H k).coherent.inputData R).terminalFrontReference n

def terminalPhase (n k : ℕ) : ℝ :=
  ((stepData R H k).coherent.inputData R).terminalFrontPhase n

def rawPath (n k : ℕ) :=
  (((stepData R H k).coherent.inputData R).pre n).geometric.rawPath

def analyticSource (n k : ℕ) :=
  (((stepData R H k).coherent.inputData R).analytic n).source

theorem terminalFront_eq_phase (n k : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (analyticSource R H n k) =
      MarkedShift.shiftData (terminalPhase R H n k)
        (terminalReference R H n k) :=
  ((stepData R H k).coherent.inputData R).terminalFront_eq_phase n

noncomputable def coherence (k : ℕ) :
    StepCoherence (fun n => raw R H n k) (fun n => raw R H n (k + 1))
      (canonical R H · k) (terminalReference R H · k) := by
  let I := (stepData R H k).phaseStep R
  exact
    { initialPhase := I.initialPhase
      nextDisplayed_eq_phase := by
        intro n
        simpa [raw, canonical, reachable_succ_nodes, I,
          PreparedStepData.phaseStep] using I.nextDisplayed_eq_phase n
      rawDiagonalRangeEdge := I.rawDiagonalRangeEdge
      terminalReference_eq := by
        intro n
        simpa [raw, terminalReference, reachable_succ_nodes, I,
          PreparedStepData.phaseStep] using I.terminalReference_eq n }

theorem rawDistance (n k : ℕ) :
    dist (raw R H n k) (canonical R H n k) ≤ R.error n k := by
  let I := (stepData R H k).coherent.inputData R
  exact (I.rawMetric n).dist_displayed_base_le.trans (I.edgeBudget_le_error n)

noncomputable def system :
    CoherentPhaseReachableMetricRange.System
      (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R) R.error where
  raw := raw R H
  canonical := canonical R H
  terminalReference := terminalReference R H
  base_eq := H.base_displayed
  coherence := coherence R H
  rawDistance := rawDistance R H

end Provider

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedReachableSystem
