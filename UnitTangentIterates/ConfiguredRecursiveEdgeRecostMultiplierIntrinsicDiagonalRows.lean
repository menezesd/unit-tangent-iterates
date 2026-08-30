import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows

/-!
# Intrinsically typed multiplier diagonal rows

A marking-aware source depends on all four scalar profile values.  Packaging a
node with those values avoids transporting analytic structures merely to
replace globally shifted profiles by propositionally equal local profiles.
Configured diagonal equalities are retained separately by the reachable
builder.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows

open ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows
  ConfiguredRecursiveEdgeRecostedCarrierRow
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource

/-- A stage together with its intrinsic profile/index type and the three
scalar values used by the configured recursive contracts.  Keeping those
contracts separate lets the physical base retain its canonical stage type. -/
structure Node where
  P0 : ℝ
  khat : ℝ
  Qmax : ℝ
  stageP0 : ℕ → ℝ
  stageKhat : ℕ → ℝ
  stageQmax : ℕ → ℝ
  stageIndex : ℕ
  stage : Stage stageP0
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    stageKhat stageQmax stageIndex

/-- One diagonal step.  The displayed metric row is `n`; the recursive source
comes from predecessor row `n+1`. -/
structure Step (S : ℕ → Node) (k : ℕ) where
  pre : ∀ n, ConfiguredRecursiveEdgeRecostedPreCarrier.Core (S n).stage
  rawMetric : ∀ n, RawMetricGeometry.Bounded (pre n).geometric
  targetP0 : ℕ → ℝ
  targetKhat : ℕ → ℝ
  targetQmax : ℕ → ℝ
  /-- The actual arclength-marked initial of the mapped source row.  It is
  generally a cyclic shift of the canonical presented base. -/
  nextDisplayed : ℕ → Data
  analytic : ∀ n, Input (pre (n + 1))
    (targetP0 n) ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (targetKhat n) (targetQmax n)
  /-- Retained terminal-front phase sidecar.  The concrete constructor fixes
  `terminalFrontReference` to the canonical next displayed representative. -/
  terminalFrontReference : ℕ → Data
  terminalFrontPhase : ℕ → ℝ
  terminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (analytic n).source =
        MarkedShift.shiftData (terminalFrontPhase n) (terminalFrontReference n)

namespace Step

noncomputable def nextApplied
    (I : Step S k) (n : ℕ) :
    Applied (I.pre (n + 1)).path (I.analytic n).source :=
  Classical.choice (exists_applied (I.analytic n).source)

noncomputable def next
    (I : Step S k) (n : ℕ) : Node where
  P0 := I.targetP0 n
  khat := I.targetKhat n
  Qmax := I.targetQmax n
  stageP0 := fun _ ↦ I.targetP0 n
  stageKhat := fun _ ↦ I.targetKhat n
  stageQmax := fun _ ↦ I.targetQmax n
  stageIndex := 0
  stage :=
    { start := (S (n + 1)).stage.displayed
      rear := (I.pre (n + 1)).geometric.output.jets.rear
      Gamma := (I.pre (n + 1)).path
      source := (I.analytic n).source
      applied := I.nextApplied n
      displayed := I.nextDisplayed n }

@[simp] theorem next_displayed
    (I : Step S k) (n : ℕ) :
    (I.next n).stage.displayed = I.nextDisplayed n := rfl

@[simp] theorem next_source
    (I : Step S k) (n : ℕ) :
    (I.next n).stage.source = (I.analytic n).source := rfl

theorem terminalRange
    (I : Step S k) (n : ℕ) :
    range ((I.next n).stage.Gamma.X (I.next n).stage.Gamma.T) =
      range (I.pre (n + 1)).geometric.output.jets.rear.1 := by
  apply congrArg range
  funext u
  exact (I.pre (n + 1)).path.finish u

end Step

/-- All-depth rowwise recursion. -/
structure Rows where
  base : ℕ → Node
  base_range : ∀ n,
    range (base n).stage.rear.1 = range (base (n + 1)).stage.displayed.1
  step : ∀ k (S : ℕ → Node), Step S k

namespace Rows

noncomputable def stages (R : Rows) : ℕ → ℕ → Node
  | 0 => R.base
  | k + 1 => (R.step k (R.stages k)).next

def P (R : Rows) (n k : ℕ) : Data :=
  (R.stages k n).stage.displayed

def edgeBudget (R : Rows) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).rawMetric n).edgeBudget

def rawBound (R : Rows) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).rawMetric n).rawBound

def endpointCap (R : Rows) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).pre n).geometric.endpointCap

def terminalFrontPhase (R : Rows) (n k : ℕ) : ℝ :=
  (R.step k (R.stages k)).terminalFrontPhase n

theorem terminalFront_eq_phase
    (R : Rows) (n k : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      ((R.step k (R.stages k)).analytic n).source =
      MarkedShift.shiftData (R.terminalFrontPhase n k)
        ((R.step k (R.stages k)).terminalFrontReference n) :=
  (R.step k (R.stages k)).terminalFront_eq_phase n

@[simp] theorem P_zero (R : Rows) (n : ℕ) :
    R.P n 0 = (R.base n).stage.displayed := rfl

@[simp] theorem P_succ (R : Rows) (n k : ℕ) :
    R.P n (k + 1) = (R.step k (R.stages k)).nextDisplayed n := rfl

end Rows

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
