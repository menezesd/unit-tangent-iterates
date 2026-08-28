import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows

/-!
# Direct recost source before physical-history completion

The direct exact source is analytic data determined by the chosen raw path.
It must be constructed before the physical history whose final node is that
source.  This module separates that analytic core from `CarrierRow`, then
packages the completed history back into the existing row API.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedPreCarrier

open ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  ConfiguredRecursiveEdgeRecostedCarrierRow
  ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
  {S : Stage P0u khu khatu Qmaxu j}
  {p0 kh0 khat0 qmax0 E C0 C1 C2 d : ℝ}

/-- The part of a carrier row fixed before its physical history is known. -/
structure Core (S : Stage P0u khu khatu Qmaxu j) where
  geometric : GeometricInput S
  eta_continuous : Continuous (uncurry geometric.output.chosen.Delta.eta)
  eta1_continuous : Continuous (uncurry geometric.output.chosen.c2.eta1)
  eta2_continuous : Continuous (uncurry geometric.output.chosen.c2.eta2)
  time_one : geometric.output.chosen.Delta.T = 1

namespace Core

def path (C : Core S) : NormalPath S.displayed C.geometric.output.jets.rear :=
  CanonicalNormalPathRecost.recost C.geometric.output.chosen.Delta
    C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
    C.eta2_continuous

end Core

/-- Exact recost successor data which does not depend on a physical history. -/
structure Input (C : Core S) (P0Next khNext khatNext QmaxNext : ℝ) where
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
    C.geometric.output.chosen eps
  eps_le_quarter : eps ≤ 1 / 4
  bounds :
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.DirectBounds
      C.geometric.output.chosen selected pre gauge shifted kh_nonnegative kh_lt_one
      scalar P0_pos C.geometric.output.chosen.c2 C.eta_continuous
      C.eta1_continuous C.eta2_continuous
  rawSlice : AnalyticSuccessorSliceFacts
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
      C.geometric.output.chosen selected pre gauge shifted kh_nonnegative kh_lt_one
      scalar P0_pos)

namespace Input

def source {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      C.path p0 kh0 khat0 qmax0 :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource
    C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
    I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
    C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
    C.eta2_continuous I.bounds

def slice {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    AnalyticSuccessorSliceFacts I.source :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSlice
    C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
    I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
    C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
    C.eta2_continuous I.bounds I.rawSlice

@[simp] theorem path_eta {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    C.path.eta = C.geometric.output.chosen.Delta.eta := by
  simpa [Core.path,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    CanonicalNormalPathRecost.recost_eta C.geometric.output.chosen.Delta
      C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
      C.eta2_continuous

@[simp] theorem source_period_eq {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    I.source.P = rearPeriod S.source := by
  rfl

@[simp] theorem source_phi1_eq {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    I.source.phi1 = C.geometric.output.chosen.phi1 := by
  rfl

def sourceJets {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.SourceNormalizedJetBounds
      I.source I.eps where
  eps_nonnegative := I.jets.eps_nonnegative
  dphi := by
    intro t ht u
    rw [I.source_phi1_eq, I.source_period_eq]
    exact I.jets.dpsi t ht u

end Input

/-- A pre-carrier after its normalized history has been constructed. -/
structure Completion (C : Core S) (I : Input C p0 kh0 khat0 qmax0)
    (E C0 C1 C2 d : ℝ) where
  V : ℕ → AnchoredJacobiStableTransition.Components
  major : ℕ → ℝ
  depth : ℕ
  splitHistory : SplitHistory C.geometric.rawPath V major depth E C0 C1 C2 d

namespace Completion

def carrier {C : Core S} {I : Input C p0 kh0 khat0 qmax0}
    (H : Completion C I E C0 C1 C2 d) : CarrierRow S E C0 C1 C2 d where
  geometric := C.geometric
  eta_continuous := C.eta_continuous
  eta1_continuous := C.eta1_continuous
  eta2_continuous := C.eta2_continuous
  time_one := C.time_one
  V := H.V
  major := H.major
  depth := H.depth
  splitHistory := H.splitHistory

/-- Erase the construction order after completion, recovering the public
diagonal-row input without any self-reference. -/
def input {C : Core S} {I : Input C p0 kh0 khat0 qmax0}
    (H : Completion C I E C0 C1 C2 d) :
    ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Input H.carrier
      p0 kh0 khat0 qmax0 where
  selected := I.selected
  pre := I.pre
  gauge := I.gauge
  shifted := I.shifted
  kh_nonnegative := I.kh_nonnegative
  kh_lt_one := I.kh_lt_one
  scalar := I.scalar
  P0_pos := I.P0_pos
  eps := I.eps
  jets := I.jets
  eps_le_quarter := I.eps_le_quarter
  bounds := I.bounds
  rawSlice := I.rawSlice

@[simp] theorem carrier_geometric {C : Core S}
    {I : Input C p0 kh0 khat0 qmax0}
    (H : Completion C I E C0 C1 C2 d) :
    H.carrier.geometric = C.geometric := rfl

@[simp] theorem input_source {C : Core S}
    {I : Input C p0 kh0 khat0 qmax0}
    (H : Completion C I E C0 C1 C2 d) :
    H.input.source = I.source := rfl

@[simp] theorem input_slice {C : Core S}
    {I : Input C p0 kh0 khat0 qmax0}
    (H : Completion C I E C0 C1 C2 d) :
    H.input.slice = I.slice := rfl

end Completion

end ConfiguredRecursiveEdgeRecostedPreCarrier
