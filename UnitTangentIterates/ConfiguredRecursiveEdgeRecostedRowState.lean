import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedAnalyticCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackPhysicalMetricSplitHistory
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource

/-!
# Dependent recursive row state with recosted carriers

This module is the structural all-depth recursion for the paper-faithful
carrier choice.  Each reachable row retains its selected terminal, split
physical history, metric package, canonical recost, transported exact source,
and exact analytic slice.  The still-local analytic and transport inputs are
fields of `Input`; no raw source-mass recurrence is asserted.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRowState

open ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource

theorem c2NormalPathData_unique
    {p q : Data} {Gamma : NormalPath p q}
    (A B : C2NormalPathData Gamma) : A = B := by
  have h1 : A.eta1 = B.eta1 := by
    funext t u
    exact (A.eta_deriv t u).unique (B.eta_deriv t u)
  have h2 : A.eta2 = B.eta2 := by
    funext t u
    apply (A.eta1_deriv t u).unique
    rw [h1]
    exact B.eta1_deriv t u
  cases A
  cases B
  cases h1
  cases h2
  rfl

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j}

/-- Stage-local geometric facts which, together with a split history, build
the complete physical metric input. -/
structure MetricGeometry (G : GeometricInput S) where
  pathP0 : ℝ
  pathP1 : ℝ
  pathKhat : ℝ
  pathG1 : ℝ
  pathCg : ℝ
  c2 : C2NormalPathData G.rawPath
  eta_continuous : Continuous (uncurry G.rawPath.eta)
  eta1_continuous : Continuous (uncurry c2.eta1)
  eta2_continuous : Continuous (uncurry c2.eta2)
  start_curve_deriv : ∀ u,
    HasDerivAt (⇑S.displayed.1) (S.displayed.2.1 u) u
  start_vel_deriv : ∀ u,
    HasDerivAt (⇑S.displayed.2.1) (S.displayed.2.2 u) u
  geometry : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
    pathP0 pathP1 pathKhat pathG1 pathCg
      (G.recost c2 eta_continuous eta1_continuous eta2_continuous)
  time_one : G.rawPath.T = 1

/-- One fully physical selected row before its successor source is
transported. -/
structure PhysicalRow
    (S : Stage P0 kh khat Qmax j) (E C0 C1 C2 d : ℝ) where
  geometric : GeometricInput S
  metricGeometry : MetricGeometry geometric
  V : ℕ → AnchoredJacobiStableTransition.Components
  major : ℕ → ℝ
  depth : ℕ
  splitHistory : SplitHistory geometric.rawPath V major depth E C0 C1 C2 d

namespace PhysicalRow

variable {E C0 C1 C2 d : ℝ} (R : PhysicalRow S E C0 C1 C2 d)

/-- The metric package is theorem-produced from the retained split history. -/
def metric : PhysicalMetricInput R.geometric E C0 C1 C2 d :=
  PhysicalMetricInput.ofSplitHistory
    R.metricGeometry.pathP0 R.metricGeometry.pathP1
    R.metricGeometry.pathKhat R.metricGeometry.pathG1
    R.metricGeometry.pathCg R.metricGeometry.c2
    R.metricGeometry.eta_continuous R.metricGeometry.eta1_continuous
    R.metricGeometry.eta2_continuous R.metricGeometry.start_curve_deriv
    R.metricGeometry.start_vel_deriv R.metricGeometry.geometry
    R.metricGeometry.time_one R.splitHistory

/-- The canonical recosted carrier backed by the same split history. -/
def carrier : CarrierInput R.geometric R.V R.major R.depth E C0 C1 C2 d where
  c2 := R.metricGeometry.c2
  eta_continuous := R.metricGeometry.eta_continuous
  eta1_continuous := R.metricGeometry.eta1_continuous
  eta2_continuous := R.metricGeometry.eta2_continuous
  time_one := R.metricGeometry.time_one
  history := HistoryCertificate.split R.splitHistory

structure ChosenRegularity where
  c2 : C2NormalPathData R.geometric.output.chosen.Delta
  eta_continuous : Continuous (uncurry R.geometric.output.chosen.Delta.eta)
  eta1_continuous : Continuous (uncurry c2.eta1)
  eta2_continuous : Continuous (uncurry c2.eta2)

theorem metric_eta1_eq_chosen :
    R.metricGeometry.c2.eta1 = R.geometric.output.chosen.c2.eta1 := by
  funext t u
  apply HasDerivAt.unique (R.metricGeometry.c2.eta_deriv t u)
  simpa only [GeometricInput.rawPath, R.geometric.output.stage_eq] using
    R.geometric.output.chosen.c2.eta_deriv t u

theorem metric_eta2_eq_chosen :
    R.metricGeometry.c2.eta2 = R.geometric.output.chosen.c2.eta2 := by
  funext t u
  apply HasDerivAt.unique (R.metricGeometry.c2.eta1_deriv t u)
  simpa only [R.metric_eta1_eq_chosen] using
    R.geometric.output.chosen.c2.eta1_deriv t u

def chosenRegularity : R.ChosenRegularity := by
  exact
    { c2 := R.geometric.output.chosen.c2
      eta_continuous := by
        simpa only [GeometricInput.rawPath, R.geometric.output.stage_eq] using
          R.metricGeometry.eta_continuous
      eta1_continuous := by
        simpa only [R.metric_eta1_eq_chosen] using
          R.metricGeometry.eta1_continuous
      eta2_continuous := by
        simpa only [R.metric_eta2_eq_chosen] using
          R.metricGeometry.eta2_continuous }

def directPath : NormalPath S.displayed R.geometric.output.jets.rear :=
  CanonicalNormalPathRecost.recost R.geometric.output.chosen.Delta
    R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
    R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous

def chosenSplitHistory :
    ConfiguredRecursiveEdgeActualPhysicalSplitHistory.SplitHistory
      R.geometric.output.chosen.Delta R.V R.major R.depth E C0 C1 C2 d := by
  let h : R.geometric.rawPath = R.geometric.output.chosen.Delta := by
    exact R.geometric.output.stage_eq
  exact h ▸ R.splitHistory

theorem chosen_time_one : R.geometric.output.chosen.Delta.T = 1 := by
  simpa only [GeometricInput.rawPath, R.geometric.output.stage_eq] using
    R.metricGeometry.time_one

def directStable :
    FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents
      R.directPath 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d :=
  R.chosenSplitHistory.toStable R.chosen_time_one R.chosenRegularity.c2
    R.chosenRegularity.eta_continuous R.chosenRegularity.eta1_continuous
    R.chosenRegularity.eta2_continuous

theorem directPath_cost_le :
    R.directPath.cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2 * d :=
  FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
    R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
    R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
    R.directStable

theorem directPath_terminal_range :
    range (R.directPath.X R.directPath.T) =
      range R.geometric.output.jets.rear.1 := by
  apply congrArg range
  funext u
  exact R.directPath.finish u

theorem carrier_terminal_range :
    range (R.carrier.path.X R.carrier.path.T) =
      range R.geometric.output.jets.rear.1 :=
  R.carrier.terminal_range

theorem carrier_cost_le :
    R.carrier.path.cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2 * d :=
  R.carrier.cost_le

theorem selectedRear_dist_base_le_endpointCap :
    dist R.geometric.output.jets.rear R.geometric.base ≤
      R.geometric.endpointCap :=
  R.geometric.rear_dist_base_le_endpointCap

end PhysicalRow

/-- The exact analytic and recost-transport inputs for one reachable physical
row.  These are the two callbacks being discharged by the exact-successor
and tangential-period estimates; all recursion below is already structural. -/
structure Input
    (R : PhysicalRow S E C0 C1 C2 d) where
  raw : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.AnalyticInput
    R.geometric
  transport :
    FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport.TransportInput
      raw.nextSource R.carrier.path
  rawSlice : AnalyticSuccessorSliceFacts raw.nextSource

namespace Input

variable {E C0 C1 C2 d : ℝ} {R : PhysicalRow S E C0 C1 C2 d}

def transported (I : Input R) :
    RawSuccessorTransportInput R.geometric R.carrier where
  raw := I.raw
  transport := I.transport

def transportedSlice (I : Input R) :
    RawSuccessorTransportInput.SliceInput I.transported where
  rawSlice := I.rawSlice

/-- The exact analytic successor consumed by any later recursive-column
adapter. -/
def exactAnalyticSuccessor (I : Input R) :
    AnalyticSuccessor R.carrier.path S.source
      (P0 (j + 1)) (kh (j + 1)) (khat (j + 1)) (Qmax (j + 1)) :=
  I.transported.exactAnalyticSuccessor I.transportedSlice

/-- The next reachable stage.  Its source carrier is the canonical recost;
its displayed datum is the canonical base following the selected rear. -/
def next (I : Input R) : Stage P0 kh khat Qmax (j + 1) :=
  I.transported.mappedStage

@[simp] theorem next_Gamma (I : Input R) :
    I.next.Gamma = R.carrier.path := rfl

@[simp] theorem next_source (I : Input R) :
    I.next.source = I.transported.nextSource := rfl

@[simp] theorem next_displayed (I : Input R) :
    I.next.displayed = R.geometric.base := rfl

theorem next_terminal_range (I : Input R) :
    range (I.next.Gamma.X I.next.Gamma.T) =
      range R.geometric.output.jets.rear.1 :=
  I.transported.mappedStage_terminal_range

end Input

/-! ## Structural all-depth recursion -/

/-- Temporary all-depth input interface.  It makes the two remaining
row-local callbacks explicit and iterates only theorem-produced `Input.next`
stages. -/
structure Provider
    (E C0 C1 C2 : ℝ) (d : ℕ → ℝ) where
  input : ∀ k (S : Stage P0 kh khat Qmax k),
    Σ R : PhysicalRow S E C0 C1 C2 (d k), Input R

noncomputable def stages
    (base : Stage P0 kh khat Qmax 0)
    (M : Provider (P0 := P0) (kh := kh) (khat := khat) (Qmax := Qmax)
      E C0 C1 C2 d) :
    ∀ k, Stage P0 kh khat Qmax k
  | 0 => base
  | k + 1 => (M.input k (stages base M k)).2.next

@[simp] theorem stages_zero
    (base : Stage P0 kh khat Qmax 0)
    (M : Provider (P0 := P0) (kh := kh) (khat := khat) (Qmax := Qmax)
      E C0 C1 C2 d) :
    stages base M 0 = base := rfl

@[simp] theorem stages_succ
    (base : Stage P0 kh khat Qmax 0)
    (M : Provider (P0 := P0) (kh := kh) (khat := khat) (Qmax := Qmax)
      E C0 C1 C2 d) (k : ℕ) :
    stages base M (k + 1) =
      (M.input k (stages base M k)).2.next := rfl

/-- Every positive-depth recursive carrier is definitionally a canonical
recost of the selected raw path at the preceding depth. -/
theorem stages_succ_Gamma
    (base : Stage P0 kh khat Qmax 0)
    (M : Provider (P0 := P0) (kh := kh) (khat := khat) (Qmax := Qmax)
      E C0 C1 C2 d) (k : ℕ) :
    (stages base M (k + 1)).Gamma =
      (M.input k (stages base M k)).1.carrier.path := rfl

/-! ## Direct nonadditive recursion -/

namespace Direct

open FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

abbrev W {E C0 C1 C2 d : ℝ} (R : PhysicalRow S E C0 C1 C2 d) :=
  R.geometric.output.chosen

/-- Exact selected-inverse construction data for the direct source.  The
canonical analytic inequalities are isolated in `bounds`; no additive source
transport occurs. -/
structure Input
    (R : PhysicalRow S E C0 C1 C2 d) where
  selected : ExactSelected S.source (kap := kh (j + 1))
  pre : PreTransport selected
  gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre)
  shifted : ShiftedTransport pre gauge
  kh_nonnegative : 0 ≤ kh (j + 1)
  kh_lt_one : kh (j + 1) < 1
  scalar : Scalar (A := S.source) (kap := kh (j + 1))
    (P0Next := P0 (j + 1)) (khatNext := khat (j + 1))
    (QmaxNext := Qmax (j + 1))
  P0_pos : 0 < P0 (j + 1)
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

namespace Input

variable {E C0 C1 C2 d : ℝ} {R : PhysicalRow S E C0 C1 C2 d}

/-- The recursive source has density exactly `recost.m / sqrt`; this is the
source installed in the next stage. -/
def source (I : Direct.Input R) :
    MarkingAwareSource R.directPath (P0 (j + 1)) (kh (j + 1))
      (khat (j + 1)) (Qmax (j + 1)) := by
  simpa [PhysicalRow.directPath,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
      R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
      R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
      I.bounds

def analyticSuccessor (I : Direct.Input R) :
    AnalyticSuccessor R.directPath S.source
      (P0 (j + 1)) (kh (j + 1)) (khat (j + 1)) (Qmax (j + 1)) := by
  simpa [PhysicalRow.directPath,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directAnalyticSuccessor
      R.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
      R.chosenRegularity.c2 R.chosenRegularity.eta_continuous
      R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
      I.bounds I.rawSlice

/-- One direct mapped row. -/
def next (I : Direct.Input R) : Stage P0 kh khat Qmax (j + 1) where
  start := S.displayed
  rear := R.geometric.output.jets.rear
  Gamma := R.directPath
  source := I.source
  applied := Classical.choice
    (FiniteSmoothRearFamilyMarkingAwareAppliedSource.exists_applied I.source)
  displayed := R.geometric.base

@[simp] theorem next_Gamma (I : Direct.Input R) :
    I.next.Gamma = R.directPath := rfl

@[simp] theorem next_source (I : Direct.Input R) :
    I.next.source = I.source := rfl

@[simp] theorem next_displayed (I : Direct.Input R) :
    I.next.displayed = R.geometric.base := rfl

theorem next_terminal_range (I : Direct.Input R) :
    range (I.next.Gamma.X I.next.Gamma.T) =
      range R.geometric.output.jets.rear.1 :=
  R.directPath_terminal_range

end Input

/-- Structural provider for the direct, nonadditive all-depth recursion. -/
structure Provider
    (E C0 C1 C2 : ℝ) (d : ℕ → ℝ) where
  input : ∀ k (S : Stage P0 kh khat Qmax k),
    Σ R : PhysicalRow S E C0 C1 C2 (d k), Direct.Input R

noncomputable def stages
    (base : Stage P0 kh khat Qmax 0)
    (M : Direct.Provider (P0 := P0) (kh := kh) (khat := khat)
      (Qmax := Qmax) E C0 C1 C2 d) :
    ∀ k, Stage P0 kh khat Qmax k
  | 0 => base
  | k + 1 => (M.input k (stages base M k)).2.next

@[simp] theorem stages_zero
    (base : Stage P0 kh khat Qmax 0)
    (M : Direct.Provider (P0 := P0) (kh := kh) (khat := khat)
      (Qmax := Qmax) E C0 C1 C2 d) :
    Direct.stages base M 0 = base := rfl

@[simp] theorem stages_succ
    (base : Stage P0 kh khat Qmax 0)
    (M : Direct.Provider (P0 := P0) (kh := kh) (khat := khat)
      (Qmax := Qmax) E C0 C1 C2 d) (k : ℕ) :
    Direct.stages base M (k + 1) =
      (M.input k (Direct.stages base M k)).2.next := rfl

theorem stages_succ_Gamma
    (base : Stage P0 kh khat Qmax 0)
    (M : Direct.Provider (P0 := P0) (kh := kh) (khat := khat)
      (Qmax := Qmax) E C0 C1 C2 d) (k : ℕ) :
    (Direct.stages base M (k + 1)).Gamma =
      (M.input k (Direct.stages base M k)).1.directPath := rfl

end Direct

end ConfiguredRecursiveEdgeRecostedRowState
