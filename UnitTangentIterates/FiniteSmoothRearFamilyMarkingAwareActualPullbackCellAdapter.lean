import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedPhysicalSidecars

/-!
# Cell-local adapter for actual pullback rows

An actual presented output already contains the physical rear/front
kinematics and the ordinary constant-speed rear.  Constructing a geometric
array cell therefore needs only the local nonaffine source facts, the exact
canonical-front identification, the common front tube, and the diagonal
range edge.  No `RowBounds` or source-mass estimate appears here.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackCellAdapter

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  NormalPathC2IncrementVariableSpeed
  VariableMarkedTube

variable {P0 kh khat Qmax : ℕ → ℕ → ℝ}
  {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

/-- Exactly the local data not already contained in an actual presented
stage. -/
structure LocalInput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) where
  P1 : ℝ
  markingLower : ℝ
  markingUpper : ℝ
  facts : Nonaffine.Facts ((R.provider n).stages k).source
    P1 markingLower markingUpper
  frontData_eq : (R.input n k).geometric.terminal.frontData =
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      ((R.provider n).stages k).source
  frontTube : IsTubeMember (commonC D) 0 (commonDlt D)
    (R.input n k).geometric.terminal.frontData
  range_edge : GeometricUnitTangentRangeEdge
    (R.P (n + 1) k) (R.P n (k + 1))

namespace LocalInput

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {R : Rows P0 kh khat Qmax E C0 C1 C2 d} {n k : ℕ}

def state (L : LocalInput D R n k) : State where
  start := ((R.provider n).stages k).start
  finish := ((R.provider n).stages k).rear
  path := ((R.provider n).stages k).Gamma
  P0 := P0 n k
  kh := kh n k
  khat := khat n k
  Qmax := Qmax n k
  source := ((R.provider n).stages k).source
  P1 := L.P1
  markingLower := L.markingLower
  markingUpper := L.markingUpper
  facts := L.facts

def row (L : LocalInput D R n k) : PresentedRow L.state.source where
  applied := ((R.provider n).stages k).applied
  p := R.P n k
  base := (R.input n k).geometric.base
  frontEndpoint := ((R.provider n).stages k).rear
  bound := (R.input n k).geometric.bound
  terminalInput := (R.input n k).geometric.terminal
  output := (R.input n k).geometric.output
  cFront := commonC D
  kFront := 0
  dFront := commonDlt D
  cFront_pos := by simpa [commonC] using D.model.separation_pos 0
  front_tube := L.frontTube
  frontData_eq := L.frontData_eq

/-- The displayed successor is definitionally the base selected by the
current geometric input. -/
theorem displayed_succ_eq_base (L : LocalInput D R n k) :
    R.P n (k + 1) = (R.input n k).geometric.base := by
  rfl

/-- Construct one exact geometric cell from a local actual stage. -/
def cell (L : LocalInput D R n k) : Cell R.P n k where
  state := L.state
  row := L.row
  kh_nonnegative := ((R.provider n).stages k).source.kh_nonnegative
  kh_lt_one := ((R.provider n).stages k).source.kh_lt_one
  selectedStart := R.P n k
  selectedEnd := R.intermediateRear n k
  path := R.recostPath n k
  physicalFrontData := (R.input n k).geometric.terminal.frontData
  physicalKinematics := ⟨by
    rw [L.displayed_succ_eq_base]
    exact (R.input n k).geometric.output.frontKinematics⟩
  physicalRearSpeedConst := by
    intro u v
    rw [L.displayed_succ_eq_base]
    exact (R.input n k).geometric.terminal.zero_floor_tube.speed_const u v
  range_edge := L.range_edge

end LocalInput

/-- A complete local cell family.  Base ordinary-tube membership and the
constant configured curvature cap are the only row-level physical inputs. -/
structure Family
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) where
  input : ∀ n k, LocalInput D R n k
  baseTube : ∀ n, IsTubeMember (commonC D) 0 (commonDlt D) (R.P n 0)
  kh_eq : ∀ n k, kh n k = sourceKh

namespace Family

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {R : Rows P0 kh khat Qmax E C0 C1 C2 d}

def cell (H : Family D R) (n k : ℕ) : Cell R.P n k :=
  (H.input n k).cell

/-- Any array whose stored cells are this local construction receives the
complete configured `CellFacts` package without additional callbacks. -/
def cellFacts
    (H : Family D R)
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {rowP0 rowP1 rowKhat rowG1 rowCg rowC : ℕ → ℝ}
    (A : Array Q R.P e rowP0 rowP1 rowKhat rowG1 rowCg rowC
      (commonC D) (commonDlt D))
    (hcell : ∀ n k, A.cell n k = H.cell n k) :
    ConfiguredRecursiveEdgePresentedPhysicalSidecars.CellFacts D A where
  baseTube := H.baseTube
  cellKh := by
    intro n k
    rw [hcell n k]
    exact H.kh_eq n k
  cellFrontTube := by
    intro n k
    rw [hcell n k]
    exact (H.input n k).frontTube

end Family

end FiniteSmoothRearFamilyMarkingAwareActualPullbackCellAdapter
