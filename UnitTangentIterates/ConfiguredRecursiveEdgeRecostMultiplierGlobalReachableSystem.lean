import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricGeometry
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStepCoherenceAdapter
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.CoherentPhaseReachableMetricRange

/-!
# Reachable global recost recursion with coherent phases

The successor is requested only for states carrying a caller-supplied
reachability certificate.  In particular, this does not assert that an
analytic successor exists for an arbitrary family of stages.  Every selected
global step retains its raw chosen metric leg, exact diagonal range edge, and
terminal-front phase witness.  The public grid is then obtained by cumulative
phase cancellation.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierGlobalReachableSystem

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}

abbrev GlobalState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 G1 Cg C Qmax : ℕ → ℝ)
    (kappaHat c dlt kappa : ℝ) :=
  State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa

/-- Only the final-tail rows are public.  The global analytic column itself is
never transported or relabeled. -/
def publicRow (n : ℕ) : ℕ := R.totalShift + n

/-- The raw metric package is already a theorem of the canonical row selected
by a global step. -/
noncomputable def rawMetric
    {X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    (G : StepInput X) (n : ℕ) :
    RawMetricGeometry.Bounded
      (ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput
        X.invariant n) :=
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry.ofCanonicalRow X.invariant n
    (G.rowBounds.P1_le n) (G.rowBounds.G1_le n) (G.rowBounds.Cg_le n)

/-- Data retained from one theorem-produced global successor. -/
structure StepData
    (Good : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa → Type)
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) where
  input : StepInput X
  edgeBudget_le_error : ∀ n,
    (rawMetric input (publicRow R n)).edgeBudget ≤ R.error n X.depth
  good_next : Good input.next

/-- A depth-indexed reachable state.  The `Good` witness is what lets the
provider consume ancestry or normalized-history data without quantifying over
unreachable columns. -/
structure Reachable
    (Good : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa → Type)
    (k : ℕ) where
  state : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa
  depth_eq : state.depth = k
  good : Good state

/-- A provider only along certified reachable states. -/
structure Provider
    (Good : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa → Type) where
  base : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa
  base_depth : base.depth = 0
  base_good : Good base
  base_displayed : ∀ n, (base.stage (publicRow R n)).displayed =
    ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R n
  step : ∀ k (Z : Reachable Good k),
    Nonempty (StepData R Good Z.state)

namespace Provider

variable
  {Good : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa → Type}
  (H : Provider R Good)

noncomputable def reachable : ∀ k, Reachable Good k
  | 0 => ⟨H.base, H.base_depth, H.base_good⟩
  | k + 1 =>
      let Z := reachable k
      let I := Classical.choice (H.step k Z)
      { state := I.input.next
        depth_eq := by
          simp [StepInput.next, State.next, Z.depth_eq]
        good := I.good_next }

noncomputable def stepData (k : ℕ) :
    StepData R Good (reachable R H k).state :=
  Classical.choice (H.step k (reachable R H k))

@[simp] theorem reachable_succ_state (k : ℕ) :
    (reachable R H (k + 1)).state = (stepData R H k).input.next := by
  simp [reachable, stepData]

def raw (n k : ℕ) : Data :=
  ((reachable R H k).state.stage (publicRow R n)).displayed

def canonical (n k : ℕ) : Data :=
  ((stepData R H k).input.rowBounds.row (publicRow R n)).presented

def terminalReference (n k : ℕ) : Data :=
  (stepData R H k).input.mappedInitial (publicRow R n + 1)

def terminalPhase (n k : ℕ) : ℝ :=
  (stepData R H k).input.mappedTerminalFront_phase (publicRow R n)

/-- Exact coherence of the selected reachable global step. -/
noncomputable def coherence (k : ℕ) :
    StepCoherence (fun n ↦ raw R H n k)
      (fun n ↦ raw R H n (k + 1))
      (canonical R H · k) (terminalReference R H · k) := by
  let A :=
    ConfiguredRecursiveEdgeRecostedScaledGeometricStepCoherenceAdapter.toStepCoherence
      (stepData R H k).input
  refine
    { initialPhase := fun n => A.initialPhase (publicRow R n)
      nextDisplayed_eq_phase := fun n => ?_
      rawDiagonalRangeEdge := fun n => ?_
      terminalReference_eq := fun n => ?_ }
  · simpa [raw, canonical, publicRow, reachable_succ_state] using
      A.nextDisplayed_eq_phase (publicRow R n)
  · simpa [raw, canonical, publicRow, Nat.add_assoc] using
      A.rawDiagonalRangeEdge (publicRow R n)
  · simpa [raw, terminalReference, publicRow, reachable_succ_state,
      Nat.add_assoc] using A.terminalReference_eq (publicRow R n)

/-- Raw chosen-path distance before cumulative phase cancellation. -/
theorem rawDistance (n k : ℕ) :
    dist (raw R H n k) (canonical R H n k) ≤
      R.error n k := by
  have hmetric :=
    (rawMetric (stepData R H k).input (publicRow R n)).dist_displayed_base_le
  exact hmetric.trans (by
    simpa [raw, canonical, core, publicRow,
      (reachable R H k).depth_eq] using
      (stepData R H k).edgeBudget_le_error n)

/-- The coherent public grid and all finite metric/range consequences. -/
noncomputable def system :
    CoherentPhaseReachableMetricRange.System
      (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R) R.error where
  raw := raw R H
  canonical := canonical R H
  terminalReference := terminalReference R H
  base_eq n := by
    exact H.base_displayed n
  coherence := coherence R H
  rawDistance := rawDistance R H

/-- The normalized terminal-front phase is retained rather than erased by the
metric system. -/
theorem terminalFront_eq_phase (n k : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        ((stepData R H k).input.scaled (publicRow R n)).source =
      MarkedShift.shiftData (terminalPhase R H n k)
        (terminalReference R H n k) :=
  (stepData R H k).input.mappedTerminalFront_eq_phase (publicRow R n)

end Provider

end ConfiguredRecursiveEdgeRecostMultiplierGlobalReachableSystem
