import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
import UnitTangentIterates.CoherentPhaseReachableMetricRange

/-!
# Reachable-only intrinsic multiplier system

This is the rowwise replacement for a global `StepInput`.  A successor is
requested only for the actually reached intrinsic layer, and therefore only
at the final-tail indices where the recost and row-budget estimates hold.
The four phase/range fields are precisely those needed to form the coherent
public grid.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O) {K0 K1 K2 : ℝ}

/-- The intrinsically typed nodes and normalized histories at one actually
reachable depth. -/
structure Reachable (k : ℕ) where
  nodes : ℕ → Node
  layer : Layer R k nodes

/-- One reachable rowwise successor.  `InputData` contains every analytic,
metric, and normalized-successor fact; the remaining four fields only retain
the cyclic marking coherence and diagonal range orientation. -/
structure StepData {k : ℕ} (Z : Reachable R k) where
  input : InputData R Z.layer
  initialPhase : ℕ → ℝ
  nextDisplayed_eq_phase : ∀ n,
    input.nextDisplayed n = MarkedShift.shiftData (initialPhase n)
      (input.pre n).geometric.base
  rawDiagonalRangeEdge : ∀ n,
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (Z.nodes (n + 1)).stage.displayed
      (input.pre n).geometric.base
  terminalReference_eq : ∀ n,
    input.terminalFrontReference n = input.nextDisplayed (n + 1)

/-- A choice is required only at reachable layers, never for an arbitrary
family of stages. -/
structure Provider (K0 K1 K2 : ℝ) where
  step : ∀ k (Z : Reachable R k), Nonempty (StepData R Z)

namespace Provider

variable (H : Provider R K0 K1 K2)

noncomputable def reachable : ∀ k, Reachable R k
  | 0 =>
      { nodes := baseNode (K0 := K0) (K1 := K1) (K2 := K2) R
        layer := ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.layer
          (K0 := K0) (K1 := K1) (K2 := K2) R }
  | k + 1 =>
      let Z := reachable k
      let I := Classical.choice (H.step k Z)
      { nodes := (I.input.step).next
        layer := I.input.nextLayer }

noncomputable def stepData (k : ℕ) : StepData R (reachable R H k) :=
  Classical.choice (H.step k (reachable R H k))

@[simp] theorem reachable_succ_nodes (k : ℕ) :
    (reachable R H (k + 1)).nodes = ((stepData R H k).input.step).next := by
  simp [reachable, stepData]

def raw (n k : ℕ) : Data :=
  ((reachable R H k).nodes n).stage.displayed

def canonical (n k : ℕ) : Data :=
  ((stepData R H k).input.pre n).geometric.base

def terminalReference (n k : ℕ) : Data :=
  (stepData R H k).input.terminalFrontReference n

def terminalPhase (n k : ℕ) : ℝ :=
  (stepData R H k).input.terminalFrontPhase n

/-- The theorem-produced raw chosen path used by the displayed metric leg. -/
def rawPath (n k : ℕ) :=
  ((stepData R H k).input.pre n).geometric.rawPath

theorem rawPath_cost_le_rawBound (n k : ℕ) :
    (rawPath R H n k).cost ≤
      ((stepData R H k).input.rawMetric n).rawBound :=
  ((stepData R H k).input.rawMetric n).cost_le

/-- Exact recursive source at the selected cell. -/
def analyticSource (n k : ℕ) :=
  ((stepData R H k).input.analytic n).source

def analyticSlice (n k : ℕ) :=
  ((stepData R H k).input.analytic n).slice

theorem terminalFront_eq_phase (n k : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (analyticSource R H n k) =
      MarkedShift.shiftData (terminalPhase R H n k)
        (terminalReference R H n k) :=
  (stepData R H k).input.terminalFront_eq_phase n

noncomputable def coherence (k : ℕ) :
    StepCoherence (fun n ↦ raw R H n k) (fun n ↦ raw R H n (k + 1))
      (canonical R H · k) (terminalReference R H · k) where
  initialPhase := (stepData R H k).initialPhase
  nextDisplayed_eq_phase n := by
    simpa [raw, canonical, reachable_succ_nodes] using
      (stepData R H k).nextDisplayed_eq_phase n
  rawDiagonalRangeEdge n := by
    exact (stepData R H k).rawDiagonalRangeEdge n
  terminalReference_eq n := by
    simpa [raw, terminalReference, reachable_succ_nodes] using
      (stepData R H k).terminalReference_eq n

/-- The configured metric bound is already part of the rowwise `InputData`;
no global source-error table is involved. -/
theorem rawDistance (n k : ℕ) :
    dist (raw R H n k) (canonical R H n k) ≤ R.error n k := by
  exact ((stepData R H k).input.rawMetric n).dist_displayed_base_le.trans
    ((stepData R H k).input.edgeBudget_le_error n)

/-- Coherent public grid extracted from the reachable intrinsic recursion. -/
noncomputable def system :
    CoherentPhaseReachableMetricRange.System (base R) R.error where
  raw := raw R H
  canonical := canonical R H
  terminalReference := terminalReference R H
  base_eq n := by
    simpa [raw, reachable, ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base]
      using (baseNode_displayed (K0 := K0) (K1 := K1) (K2 := K2) R n)
  coherence := coherence R H
  rawDistance := rawDistance R H

end Provider

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem
