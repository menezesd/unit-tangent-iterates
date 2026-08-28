import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedPhysicalSidecars

/-!
# Cell-local adapter for synchronized actual pullback rows

The synchronized recurrence already proves the diagonal range edge.  A
geometric array cell therefore requires only the local nonaffine facts, the
terminal-front identification, and the common ordinary front tube.  No
`RowBounds`, source-mass estimate, or external range callback is used.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedCellAdapter

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  NormalPathC2IncrementVariableSpeed
  VariableMarkedTube

variable {P0 kh khat Qmax : ℕ → ℕ → ℝ}
  {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

/-- The local data not already stored in a synchronized actual stage. -/
structure LocalInput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) where
  P1 : ℝ
  markingLower : ℝ
  markingUpper : ℝ
  facts : Nonaffine.Facts (R.stages k n).source
    P1 markingLower markingUpper
  frontData_eq : (R.input n k).terminal.frontData =
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (R.stages k n).source
  frontTube : IsTubeMember (commonC D) 0 (commonDlt D)
    (R.input n k).terminal.frontData

namespace LocalInput

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {R : Rows P0 kh khat Qmax E C0 C1 C2 d} {n k : ℕ}

def state (L : LocalInput D R n k) : State where
  start := (R.stages k n).start
  finish := (R.stages k n).rear
  path := (R.stages k n).Gamma
  P0 := P0 n k
  kh := kh n k
  khat := khat n k
  Qmax := Qmax n k
  source := (R.stages k n).source
  P1 := L.P1
  markingLower := L.markingLower
  markingUpper := L.markingUpper
  facts := L.facts

def row (L : LocalInput D R n k) : PresentedRow L.state.source where
  applied := (R.stages k n).applied
  p := R.P n k
  base := (R.input n k).base
  frontEndpoint := (R.stages k n).rear
  bound := (R.input n k).bound
  terminalInput := (R.input n k).terminal
  output := (R.input n k).output
  cFront := commonC D
  kFront := 0
  dFront := commonDlt D
  cFront_pos := by simpa [commonC] using D.model.separation_pos 0
  front_tube := L.frontTube
  frontData_eq := L.frontData_eq

theorem displayed_succ_eq_base (L : LocalInput D R n k) :
    R.P n (k + 1) = (R.input n k).base := by
  rfl

/-- Construct one exact cell on the synchronized displayed grid. -/
def cell (L : LocalInput D R n k) : Cell R.P n k where
  state := L.state
  row := L.row
  kh_nonnegative := (R.stages k n).source.kh_nonnegative
  kh_lt_one := (R.stages k n).source.kh_lt_one
  selectedStart := R.P n k
  selectedEnd := R.intermediateRear n k
  path := R.recostPath n k
  physicalFrontData := (R.input n k).terminal.frontData
  physicalKinematics := ⟨by
    rw [L.displayed_succ_eq_base]
    exact (R.input n k).output.frontKinematics⟩
  physicalRearSpeedConst := by
    intro u v
    rw [L.displayed_succ_eq_base]
    exact (R.input n k).terminal.zero_floor_tube.speed_const u v
  range_edge := R.range_edge n k

end LocalInput

/-- A complete synchronized family of local cells. -/
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

/-- Derive the configured physical cell facts from the synchronized local
family. -/
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

end FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedCellAdapter
