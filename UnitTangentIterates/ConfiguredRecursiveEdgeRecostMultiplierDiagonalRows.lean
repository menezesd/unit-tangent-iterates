import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledPreCarrier

/-!
# Rowwise multiplier-aware recost diagonal

This is the sound synchronized carrier used by the final construction.  The
raw chosen path supplies the displayed metric edge in row `n`; the canonical
recost source is constructed from row `n+1`, at the identical diagonal index
`n + k + 1`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows

open ConfiguredRecursiveEdgeRecostedCarrierRow
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

namespace Profiles

abbrev P0 := ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0
abbrev kh := ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh
abbrev khat := ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat
abbrev Qmax := ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax

end Profiles

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
  {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
    P0u khu khatu Qmaxu j}
  {E C0 C1 C2 d : ℝ}

/-- Forget only the history packaging of a carrier row.  The chosen geometry,
canonical recost path, and exact regularity are unchanged. -/
def core (R : CarrierRow S E C0 C1 C2 d) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core S where
  geometric := R.geometric
  eta_continuous := R.eta_continuous
  eta1_continuous := R.eta1_continuous
  eta2_continuous := R.eta2_continuous
  time_one := R.time_one

variable {D : ConstructedConfiguredSequenceWeighted.Data} {k : ℕ}
  {SF : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n k}
  {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}

/-- One synchronized multiplier step.  No `Applied` callback is retained:
every marking-aware source has its canonical application witness. -/
structure Step
    (D : ConstructedConfiguredSequenceWeighted.Data) {k : ℕ}
    (S : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
      (Profiles.khat D) (Profiles.Qmax D) n k)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  carrier : ∀ n, CarrierRow (S n).asUnary
    (E0 n) (C00 n) (C10 n) (C20 n) (d0 n k)
  rawMetric : ∀ n, RawMetricGeometry.Bounded (carrier n).geometric
  analytic : ∀ n, Input (core (carrier (n + 1)))
    (Profiles.P0 D n (k + 1)) (Profiles.kh D n (k + 1))
    (Profiles.khat D n (k + 1)) (Profiles.Qmax D n (k + 1))

namespace Step

noncomputable def nextApplied (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    Applied (core (I.carrier (n + 1))).path (I.analytic n).source :=
  Classical.choice (exists_applied (I.analytic n).source)

noncomputable def next (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    Stage (Profiles.P0 D) (Profiles.kh D)
      (Profiles.khat D) (Profiles.Qmax D) n (k + 1) where
  start := (SF (n + 1)).displayed
  rear := (I.carrier (n + 1)).geometric.output.jets.rear
  Gamma := (core (I.carrier (n + 1))).path
  source := (I.analytic n).source
  applied := I.nextApplied n
  displayed := (I.carrier n).geometric.base

@[simp] theorem next_displayed
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    (I.next n).displayed = (I.carrier n).geometric.base := rfl

@[simp] theorem next_Gamma
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    (I.next n).Gamma = (core (I.carrier (n + 1))).path := rfl

theorem displayedDistance
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    dist (SF n).displayed (I.next n).displayed ≤
      (I.rawMetric n).edgeBudget :=
  (I.rawMetric n).dist_displayed_base_le

theorem terminalRange
    (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    range ((I.next n).Gamma.X (I.next n).Gamma.T) =
      range (I.carrier (n + 1)).geometric.output.jets.rear.1 :=
  (I.carrier (n + 1)).terminal_range

end Step

/-- All-depth triangular family with multiplier recost sources. -/
structure Rows
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  base : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n 0
  base_range : ∀ n, range (base n).rear.1 = range (base (n + 1)).displayed.1
  step : ∀ k (S : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n k),
    Step D S E0 C00 C10 C20 d0

namespace Rows

noncomputable def stages
    (R : Rows D E0 C00 C10 C20 d0) : ∀ k n,
      Stage (Profiles.P0 D) (Profiles.kh D)
        (Profiles.khat D) (Profiles.Qmax D) n k
  | 0, n => R.base n
  | k + 1, n => (R.step k (R.stages k)).next n

def P (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : Data :=
  (R.stages k n).displayed

def edgeBudget (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).rawMetric n).edgeBudget

def rawBound (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).rawMetric n).rawBound

def endpointCap (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).carrier n).geometric.endpointCap

def recostPath (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    NormalPath (R.P n k)
      ((R.step k (R.stages k)).carrier n).geometric.output.jets.rear :=
  (core ((R.step k (R.stages k)).carrier n)).path

@[simp] theorem P_zero (R : Rows D E0 C00 C10 C20 d0) (n : ℕ) :
    R.P n 0 = (R.base n).displayed := rfl

@[simp] theorem P_succ (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    R.P n (k + 1) = ((R.step k (R.stages k)).carrier n).geometric.base := rfl

theorem stepDistance (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    dist (R.P n k) (R.P n (k + 1)) ≤ R.edgeBudget n k :=
  (R.step k (R.stages k)).displayedDistance n

theorem recostPath_terminal_range
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    range ((R.recostPath n k).X (R.recostPath n k).T) =
      range ((R.step k (R.stages k)).carrier n).geometric.output.jets.rear.1 :=
  ((R.step k (R.stages k)).carrier n).terminal_range

theorem endpointCap_nonnegative
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    0 ≤ R.endpointCap n k :=
  ((R.step k (R.stages k)).carrier n).geometric.endpointCap_nonnegative

end Rows

end ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows
