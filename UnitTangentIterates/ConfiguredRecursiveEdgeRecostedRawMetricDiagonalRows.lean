import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCarrierRow
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackRawMetric
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricGeometry

/-!
# Truthful diagonal rows: raw metric leg, recost source carrier
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows

open ConfiguredRecursiveEdgeRecostedCarrierRow
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
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
  {E C0 C1 C2 d p0 kh0 khat0 qmax0 : ℝ}

structure Input
    (R : CarrierRow S E C0 C1 C2 d)
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
  eps : ℝ
  jets : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
    R.geometric.output.chosen eps
  eps_le_quarter : eps ≤ 1 / 4
  bounds :
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.DirectBounds
      R.geometric.output.chosen selected pre gauge shifted
      kh_nonnegative kh_lt_one scalar P0_pos R.geometric.output.chosen.c2 R.eta_continuous
      R.eta1_continuous R.eta2_continuous
  rawSlice : AnalyticSuccessorSliceFacts
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
      R.geometric.output.chosen selected pre gauge shifted
      kh_nonnegative kh_lt_one scalar P0_pos)

namespace Input

def source (I : Input R p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      R.path p0 kh0 khat0 qmax0 := by
  simpa [CarrierRow.path,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos R.geometric.output.chosen.c2
      R.eta_continuous R.eta1_continuous R.eta2_continuous I.bounds

def slice (I : Input R p0 kh0 khat0 qmax0) :
    AnalyticSuccessorSliceFacts I.source := by
  simpa [source, CarrierRow.path,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSlice
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos R.geometric.output.chosen.c2
      R.eta_continuous R.eta1_continuous R.eta2_continuous I.bounds I.rawSlice

@[simp] theorem path_eta (I : Input R p0 kh0 khat0 qmax0) :
    R.path.eta = R.geometric.output.chosen.Delta.eta := by
  rfl

theorem source_period_eq
    {P0' kh' khat' Qmax' : ℕ → ℝ} {j' : ℕ}
    {S' : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
      P0' kh' khat' Qmax' j'}
    {E' C0' C1' C2' d' : ℝ}
    {R' : CarrierRow S' E' C0' C1' C2' d'}
    (I : Input R' p0 kh0 khat0 qmax0) :
    I.source.P = rearPeriod S'.source := by
  rfl

theorem source_phi1_eq (I : Input R p0 kh0 khat0 qmax0) :
    I.source.phi1 = R.geometric.output.chosen.phi1 := by
  rfl

/-- The predecessor chosen jet bound transfers to the canonical recost
source.  Unlike the older generic adapter, this statement does not falsely
require the target source to live on the raw chosen path. -/
def sourceNormalizedJetBounds
    {eps : ℝ} (I : Input R p0 kh0 khat0 qmax0)
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      R.geometric.output.chosen eps) :
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.SourceNormalizedJetBounds
      I.source eps where
  eps_nonnegative := J.eps_nonnegative
  dphi := by
    intro t ht u
    rw [I.source_phi1_eq, I.source_period_eq]
    exact J.dpsi t ht u

def sourceJets (I : Input R p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.SourceNormalizedJetBounds
      I.source I.eps :=
  I.sourceNormalizedJetBounds I.jets

def nonaffineFacts
    (I : Input R p0 kh0 khat0 qmax0) {P1 : ℝ}
    (hP1 : I.slice.periodUpper ≤ P1) :
    FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts
      I.source P1 I.slice.markingLower I.slice.markingUpper :=
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts.ofAnalytic
    I.slice hP1

def targetFunctional (I : Input R p0 kh0 khat0 qmax0) :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable R.path.eta := by
  simpa [CarrierRow.path] using
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
      R.geometric.output.chosen

end Input

structure Step
    (D : ConstructedConfiguredSequenceWeighted.Data) {k : ℕ}
    (S : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
      (Profiles.khat D) (Profiles.Qmax D) n k)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  carrier : ∀ n, CarrierRow (S n).asUnary
    (E0 n) (C00 n) (C10 n) (C20 n) (d0 n k)
  rawMetric : ∀ n,
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (carrier n).geometric
  analytic : ∀ n, Input (carrier (n + 1))
    (Profiles.P0 D n (k + 1)) (Profiles.kh D n (k + 1))
    (Profiles.khat D n (k + 1)) (Profiles.Qmax D n (k + 1))
  nextApplied : ∀ n, Applied (carrier (n + 1)).path (analytic n).source

namespace Step

variable {D : ConstructedConfiguredSequenceWeighted.Data} {k : ℕ}
  {SF : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n k}
  {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}

def next (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    Stage (Profiles.P0 D) (Profiles.kh D)
      (Profiles.khat D) (Profiles.Qmax D) n (k + 1) where
  start := (SF (n + 1)).displayed
  rear := (I.carrier (n + 1)).geometric.output.jets.rear
  Gamma := (I.carrier (n + 1)).path
  source := (I.analytic n).source
  applied := I.nextApplied n
  displayed := (I.carrier n).geometric.base

theorem displayedDistance (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    dist (SF n).displayed (I.next n).displayed ≤
      (I.rawMetric n).edgeBudget := by
  exact (I.rawMetric n).dist_displayed_base_le

theorem terminalRange (I : Step D SF E0 C00 C10 C20 d0) (n : ℕ) :
    range ((I.next n).Gamma.X (I.next n).Gamma.T) =
      range (I.carrier (n + 1)).geometric.output.jets.rear.1 :=
  (I.carrier (n + 1)).terminal_range

end Step

structure Rows
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  base : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n 0
  base_range : ∀ n, range (base n).rear.1 = range (base (n + 1)).displayed.1
  step : ∀ k (S : ∀ n, Stage (Profiles.P0 D) (Profiles.kh D)
    (Profiles.khat D) (Profiles.Qmax D) n k), Step D S E0 C00 C10 C20 d0

namespace Rows

def stages (R : Rows D E0 C00 C10 C20 d0) : ∀ k n,
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
  ((R.step k (R.stages k)).carrier n).path

def rangeEdge (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :=
  ((R.step k (R.stages k)).carrier n).geometric.output.stage.range_edge

@[simp] theorem P_zero (R : Rows D E0 C00 C10 C20 d0) (n : ℕ) :
    R.P n 0 = (R.base n).displayed := rfl

@[simp] theorem P_succ (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    R.P n (k + 1) = ((R.step k (R.stages k)).next n).displayed := rfl

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

end ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
