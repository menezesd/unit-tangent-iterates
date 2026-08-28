import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRowAssembly
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

/-!
# Diagonal-shift recursion with canonical recosted carriers

The source stage `(n+1,k)` and target stage `(n,k+1)` have the same diagonal
`q=n+k+1`.  Consequently the analytic target is supplied explicitly rather
than through the row-frozen unary successor index.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDiagonalRows

open ConfiguredRecursiveEdgeRecostedRowState
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

namespace Sync

open FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

def P0 (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D (n + k)

def kh (_D : ConstructedConfiguredSequenceWeighted.Data) (_n _k : ℕ) : ℝ :=
  ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh

def khat (D : ConstructedConfiguredSequenceWeighted.Data) (_n _k : ℕ) : ℝ :=
  ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D

def Qmax (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D (n + k)

@[simp] theorem P0_diagonal (D : ConstructedConfiguredSequenceWeighted.Data)
    (n k : ℕ) : P0 D (n + 1) k = P0 D n (k + 1) := by
  simp [P0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem Qmax_diagonal (D : ConstructedConfiguredSequenceWeighted.Data)
    (n k : ℕ) : Qmax D (n + 1) k = Qmax D n (k + 1) := by
  simp [Qmax, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Sync

variable {p0 kh0 khat0 qmax0 : ℝ}
  {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
  {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
    P0u khu khatu Qmaxu j}
  {E C0 C1 C2 d : ℝ}

/-- A direct exact successor whose four target profiles are independent of
the unary index used to view the source stage. -/
structure DiagonalInput
    (R : PhysicalRow S E C0 C1 C2 d)
    (P0Next khNext khatNext QmaxNext : ℝ) where
  selected : ExactSelected S.source (kap := khNext)
  pre : PreTransport selected
  gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre)
  shifted : ShiftedTransport pre gauge
  kh_nonnegative : 0 ≤ khNext
  kh_lt_one : khNext < 1
  scalar : Scalar (A := S.source) (kap := khNext)
    (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
  P0_pos : 0 < P0Next
  bounds :
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.DirectBounds
      R.geometric.output.chosen selected pre gauge shifted
      kh_nonnegative kh_lt_one scalar P0_pos R.chosenRegularity.c2
      R.chosenRegularity.eta_continuous R.chosenRegularity.eta1_continuous
      R.chosenRegularity.eta2_continuous
  rawSlice : AnalyticSuccessorSliceFacts
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
      R.geometric.output.chosen selected pre gauge shifted
      kh_nonnegative kh_lt_one scalar P0_pos)

namespace DiagonalInput

def source
    (I : DiagonalInput R p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      R.directPath p0 kh0 khat0 qmax0 := by
  simpa [PhysicalRow.directPath,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
      R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
      R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
      I.bounds

def slice
    (I : DiagonalInput R p0 kh0 khat0 qmax0) :
    AnalyticSuccessorSliceFacts I.source := by
  simpa [source, PhysicalRow.directPath,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSlice
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
      R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
      R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
      I.bounds I.rawSlice

end DiagonalInput

open FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

/-- One synchronized diagonal recost step.  Physical metric data at row `n`
controls the displayed edge, while the source carried by row `n+1` produces
the next recursive carrier at the same diagonal. -/
structure Step
    (D : ConstructedConfiguredSequenceWeighted.Data) {k : ℕ}
    (S : ∀ n, Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n k)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  physical : ∀ n, PhysicalRow (S n).asUnary
    (E0 n) (C00 n) (C10 n) (C20 n) (d0 n k)
  analytic : ∀ n,
    DiagonalInput (physical (n + 1))
      (Sync.P0 D n (k + 1)) (Sync.kh D n (k + 1))
      (Sync.khat D n (k + 1)) (Sync.Qmax D n (k + 1))
  nextApplied : ∀ n, Applied (physical (n + 1)).directPath (analytic n).source

namespace Step

variable {D : ConstructedConfiguredSequenceWeighted.Data} {k : ℕ}
  {SF : ∀ n, Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n k}
  {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}

def next
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n (k + 1) where
  start := (SF (n + 1)).displayed
  rear := (I.physical (n + 1)).geometric.output.jets.rear
  Gamma := (I.physical (n + 1)).directPath
  source := (I.analytic n).source
  applied := I.nextApplied n
  displayed := (I.physical n).geometric.base

@[simp] theorem next_displayed
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    (I.next n).displayed = (I.physical n).geometric.base := rfl

@[simp] theorem next_Gamma
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    (I.next n).Gamma = (I.physical (n + 1)).directPath := rfl

theorem next_terminal_range
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    range ((I.next n).Gamma.X (I.next n).Gamma.T) =
      range (I.physical (n + 1)).geometric.output.jets.rear.1 :=
  (I.physical (n + 1)).directPath_terminal_range

end Step

/-- All-depth triangular diagonal recursion. -/
structure Rows
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  base : ∀ n, Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n 0
  base_range : ∀ n, range (base n).rear.1 = range (base (n + 1)).displayed.1
  step : ∀ k (S : ∀ n,
    Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n k),
    Step D S E0 C00 C10 C20 d0

namespace Rows

def stages
    (R : Rows D E0 C00 C10 C20 d0) : ∀ k n,
      Stage (Sync.P0 D) (Sync.kh D) (Sync.khat D) (Sync.Qmax D) n k
  | 0, n => R.base n
  | k + 1, n => (R.step k (R.stages k)).next n

def P (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : Data :=
  (R.stages k n).displayed

def recostPath (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    NormalPath (R.P n k)
      ((R.step k (R.stages k)).physical n).geometric.output.jets.rear :=
  ((R.step k (R.stages k)).physical n).directPath

def endpointCap (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).physical n).geometric.endpointCap

def edgeBudget (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).physical n).metric.edgeBudget

@[simp] theorem stages_zero (R : Rows D E0 C00 C10 C20 d0) (n : ℕ) :
    R.stages 0 n = R.base n := rfl

@[simp] theorem stages_succ (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    R.stages (k + 1) n = (R.step k (R.stages k)).next n := rfl

@[simp] theorem P_zero (R : Rows D E0 C00 C10 C20 d0) (n : ℕ) :
    R.P n 0 = (R.base n).displayed := rfl

@[simp] theorem P_succ (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    R.P n (k + 1) =
      ((R.step k (R.stages k)).physical n).geometric.base := rfl

theorem carrier_terminal_range
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    range ((R.stages (k + 1) n).Gamma.X (R.stages (k + 1) n).Gamma.T) =
      range ((R.step k (R.stages k)).physical (n + 1)).geometric.output.jets.rear.1 :=
  (R.step k (R.stages k)).next_terminal_range n

theorem stepDistance
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    dist (R.P n k) (R.P n (k + 1)) ≤ R.edgeBudget n k := by
  change dist (R.stages k n).displayed
      ((R.step k (R.stages k)).physical n).geometric.base ≤ _
  exact ((R.step k (R.stages k)).physical n).metric.dist_displayed_base_le_edgeBudget

theorem endpointCap_nonnegative
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    0 ≤ R.endpointCap n k :=
  ((R.step k (R.stages k)).physical n).geometric.endpointCap_nonnegative

end Rows

end ConfiguredRecursiveEdgeRecostedDiagonalRows
