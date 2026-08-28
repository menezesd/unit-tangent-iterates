import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalFrontData
import UnitTangentIterates.ConfiguredCompatiblePhysicalRearSequence
import UnitTangentIterates.MarkingAwareSourceSelectedRearData

/-! # Transition-free presented geometric recursion

This recursion retains the actual selected paths and their marking-aware
sources.  It does not package them as a `ColumnStep`: the canonical arclength
marking of a composed source agrees with the preceding selected rear only in
range, not as marked `Data`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyPhysicalFront
  GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

theorem range_shiftData (p : Data) (b : ℝ) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - b, by simp [MarkedShift.shiftData, MarkedShift.shiftMap]⟩

theorem range_geometricUnitTangent_shiftData (p : Data) (b : ℝ) :
    range (VariableMarkedTube.geometricUnitTangent
      (MarkedShift.shiftData b p)) =
      range (VariableMarkedTube.geometricUnitTangent p) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + b, by
      simp [VariableMarkedTube.geometricUnitTangent,
        MarkedShift.shiftData, MarkedShift.shiftMap]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - b, by
      simp [VariableMarkedTube.geometricUnitTangent,
        MarkedShift.shiftData, MarkedShift.shiftMap]⟩

/-- A geometric column with the actual source paths.  `current` is a range
representative; `initial` is the arclength marking used by the constructor. -/
structure GeometricCorrelatedColumn
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) (kh Qmax : ℕ → ℝ) where
  pathStart : ℕ → Data
  pathEnd : ℕ → Data
  path : ∀ n, NormalPath (pathStart n) (pathEnd n)
  source : ∀ n, MarkingAwareSource
    (path n) (P0 (n + k)) (kh n) (khat n) (Qmax (n + k))
  initial : ∀ n, Data
  initial_eq : ∀ n u, (initial n).1 u =
    RearOwnArclength.rearOwn (source n).F (source n).Theta
      (source n).delta (source n).sf 0 (rearPeriod (source n) 0 * u)
  initial_range : ∀ n, range (initial n).1 = range (current n).1
  /-- The terminal front of source path `n` is the unit-tangent front of the
  next source-initial rear. -/
  pathEndRange : ∀ n, range (pathEnd n).1 = range (initial (n + 1)).1

/-- One transition-free selected presented row. -/
structure GeometricPresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) where
  presented : Data
  applied : Applied (S.path n) (S.source n)
  terminalInput : PresentedTerminalInputCore
    (p := S.initial n) (base := presented) (bound := e n (k + 1)) applied
  output : PresentedOutputCore applied terminalInput
  front_range : range (ev terminalInput.frontData) = range (S.pathEnd n).1
  increment_geometry : IsVariableSpeedNormalPath
    (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) output.chosen.Delta
  terminal_perim_ge_one : 1 ≤ perim presented

/-- Canonical finite Harnack certificate of a geometric row. -/
def GeometricPresentedRowSelection.presentedHarnack
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : GeometricPresentedRowSelection (n := n) S) :
    VariableMarkedTube.ArclengthHarnackCertificate R.presented where
  q := R.presented
  c := R.terminalInput.physical.cq
  dlt := R.terminalInput.physical.dlt
  c_pos := R.terminalInput.physical.cq_pos
  dlt_pos := R.terminalInput.dlt_pos
  tube := R.terminalInput.zero_floor_tube
  same_range := rfl
  strictness := R.terminalInput.strict

/-- Exact cap data consumed by the endpoint-defect argument. -/
structure GeometricPresentedRowCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : GeometricPresentedRowSelection (n := n) S)
    (M endpoint defect : ℝ) : Prop where
  cost_le_M : R.output.chosen.Delta.cost ≤ M
  coefficient_le :
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      R.terminalInput.Lmax (rearPeriod (S.source n) 0)
      (rearKappa1 (kh n)) (rearKappa2 (kh n)) M
      R.terminalInput.physical.L R.terminalInput.physical.kb
      R.terminalInput.physical.kL ≤ endpoint
  cost_le_defect : R.output.chosen.Delta.cost ≤ defect

/-- The retained marking estimate linearizes the geometric row cap. -/
theorem GeometricPresentedRowCap.endpoint_dist_le
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {R : GeometricPresentedRowSelection (n := n) S}
    {M endpoint defect : ℝ} (hM : 0 ≤ M)
    (H : GeometricPresentedRowCap R M endpoint defect) :
    dist R.output.jets.rear R.presented ≤ endpoint * defect := by
  have hL : 0 ≤ R.terminalInput.physical.L := by
    rw [← R.terminalInput.physical.perim_eq]
    exact zero_le_one.trans R.terminal_perim_ge_one
  have hkb : 0 ≤ R.terminalInput.physical.kb :=
    (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
      (R.terminalInput.physical.curvature_bound 0)
  have hkL : 0 ≤ R.terminalInput.physical.kL := by
    have HL := R.terminalInput.physical.curvature_lipschitz 0 1
    have H0 := (abs_nonneg
      (R.terminalInput.physical.curvature 0 -
        R.terminalInput.physical.curvature 1)).trans HL
    norm_num at H0
    exact H0
  have hlinear : dist R.output.jets.rear R.presented ≤
      InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
        R.terminalInput.Lmax (rearPeriod (S.source n) 0)
        (rearKappa1 (kh n)) (rearKappa2 (kh n)) M
        R.terminalInput.physical.L R.terminalInput.physical.kb
        R.terminalInput.physical.kL * R.output.chosen.Delta.cost := by
    apply R.output.endpoint_dist.trans
    apply InterpolationVariableSpeedSelInvAdapter.markingC2Bound_flow_le_linear
    · exact ((S.source n).rear_period_pos 0).le.trans
        (R.terminalInput.rearPeriod_le 0)
    · exact ((S.source n).rear_period_pos 0).le
    · exact rearKappa1_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one
    · exact rearKappa2_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one
    · exact hM
    · exact hL
    · exact hkb
    · exact hkL
    · exact R.output.chosen.Delta.cost_nonneg
    · exact H.cost_le_M
  have hcanonical : 0 ≤
      InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
        R.terminalInput.Lmax (rearPeriod (S.source n) 0)
        (rearKappa1 (kh n)) (rearKappa2 (kh n)) M
        R.terminalInput.physical.L R.terminalInput.physical.kb
        R.terminalInput.physical.kL :=
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst_nonneg
      (((S.source n).rear_period_pos 0).le.trans
        (R.terminalInput.rearPeriod_le 0))
      (rearKappa1_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one)
  exact hlinear.trans
    (mul_le_mul H.coefficient_le H.cost_le_defect
      R.output.chosen.Delta.cost_nonneg
      (hcanonical.trans H.coefficient_le))

/-- All selected rows and the exact composition-stable successor sources. -/
structure GeometricPresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) where
  row : ∀ n, GeometricPresentedRowSelection (n := n) S
  compositionAnalytic : ∀ n, CompositionRecursiveAnalyticSuccessor
    (row (n + 1)).output.chosen.Delta (S.source (n + 1))
    (P0 (n + (k + 1))) (kh n) (khat n) (Qmax (n + (k + 1)))
  mappedInitial : ∀ n, Data
  mappedInitial_eq : ∀ n u, (mappedInitial n).1 u =
    RearOwnArclength.rearOwn (compositionAnalytic n).source.F
      (compositionAnalytic n).source.Theta (compositionAnalytic n).source.delta
      (compositionAnalytic n).source.sf 0
      (rearPeriod (compositionAnalytic n).source 0 * u)
  /-- The new source initial rear is a coherent cyclic phase of the canonical
  constant-speed presented terminal representative. -/
  mappedInitial_phase : ∀ n, ℝ
  mappedInitial_eq_phase : ∀ n, mappedInitial n =
    MarkedShift.shiftData (mappedInitial_phase n) (row n).presented
  mappedInitialRange : ∀ n,
    range (mappedInitial n).1 = range (row n).output.jets.rear.1
  /-- The mapped sources retain the exact predecessor orbit: their canonical
  terminal fronts are the next mapped source-initial rears. -/
  mappedTerminalFront_phase : ∀ n, ℝ
  mappedTerminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (compositionAnalytic n).source = MarkedShift.shiftData
        (mappedTerminalFront_phase n) (mappedInitial (n + 1))
  mappedNextFront_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
      (compositionAnalytic (n + 1)).source 0 =
      ev (mappedInitial (n + 1))
  mappedNextPeriod_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (compositionAnalytic (n + 1)).source 0 =
      perim (mappedInitial (n + 1))
  /-- The actual mapped initial representative remains in the fixed row tube. -/
  mappedInitialTube : ∀ n, VariableMarkedTube.IsVariableTubeMember
    c (C n) 0 dlt (mappedInitial n)
  /-- Exact provenance of the time-zero arclength scale. -/
  mappedRearPeriod_zero_eq_initial_perim : ∀ n,
    rearPeriod (compositionAnalytic n).source 0 = perim (mappedInitial n)
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(row (n + 1)).output.chosen.Delta.T,
      (compositionAnalytic n).source.m t) ≤ e n ((k + 1) + 1)
  mappedPeriodUpper_le : ∀ n,
    (compositionAnalytic n).slice.periodUpper ≤ P1 n
  mappedRearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (compositionAnalytic n).source t s| ≤ kh n
  mappedFrontPeriodScaleOne : ∀ n t,
    1 ≤ Real.sqrt (1 - (kh n) ^ 2) * (compositionAnalytic n).source.P t

/-- The mapped column uses row `n+1` as source path `n`; its current range
representative is row `n`'s selected rear. -/
def GeometricPresentedRowFamily.mappedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (F : GeometricPresentedRowFamily S) :
    GeometricCorrelatedColumn Q (fun n => (F.row n).presented)
      e (k + 1) P0 P1 khat G1 Cg C c dlt kh Qmax where
  pathStart n := S.initial (n + 1)
  pathEnd n := (F.row (n + 1)).output.jets.rear
  path n := (F.row (n + 1)).output.chosen.Delta
  source n := (F.compositionAnalytic n).source
  initial := F.mappedInitial
  initial_eq := F.mappedInitial_eq
  initial_range n := by
    rw [F.mappedInitial_eq_phase n]
    exact range_shiftData _ _
  pathEndRange n := (F.mappedInitialRange (n + 1)).symm

/-- Exact source invariant retained at every reachable geometric column. -/
structure GeometricCompositionInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax) where
  slice : ∀ n, AnalyticSuccessorSliceFacts (S.source n)
  periodUpper_le : ∀ n, (slice n).periodUpper ≤ P1 n
  /-- Intrinsic rear curvature stays inside the next selection strip. -/
  rearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (S.source n) t s| ≤ kh n
  frontPeriodScaleOne : ∀ n t,
    1 ≤ Real.sqrt (1 - (kh n) ^ 2) * (S.source n).P t
  spatial : ∀ n, SpatialFrameRegularity
    (S.path n) (S.source n).Ydot (S.source n).Theta (S.source n).delta
    (S.source n).sf (S.source n).P (S.source n).m (kh n) (Qmax (n + k))
  sidecars : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars.RecursiveExactSidecars
      (S.source n)
  terminalCurvature_nonnegative : ∀ n s,
    0 ≤ (S.source n).K (S.path n).T s
  terminalRange : ∀ n,
    range ((S.source n).F (S.path n).T) = range (S.pathEnd n).1
  /-- Exact constant-speed predecessor linkage, stronger than terminal range. -/
  terminalFront_phase : ∀ n, ℝ
  terminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (S.source n) = MarkedShift.shiftData
        (terminalFront_phase n) (S.initial (n + 1))
  nextFront_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front (S.source (n + 1)) 0 =
      ev (S.initial (n + 1))
  nextPeriod_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period (S.source (n + 1)) 0 =
      perim (S.initial (n + 1))
  /-- The source-initial representative stays in the fixed row tube. -/
  initialTube : ∀ n, VariableMarkedTube.IsVariableTubeMember
    c (C n) 0 dlt (S.initial n)
  /-- The arclength-marked initial rear also retains an ordinary tube
  certificate.  Unlike the variable tube above, this is stable here because
  every recursive initial is an explicit cyclic shift of a constant-speed
  presented rear. -/
  initialOrdinaryTube : ∀ n, ∃ c0 d0 : ℝ,
    0 < c0 ∧ IsTubeMember c0 0 d0 (S.initial n)
  /-- The intrinsic time-zero rear scale is exactly the marked perimeter. -/
  rearPeriod_zero_eq_initial_perim : ∀ n,
    rearPeriod (S.source n) 0 = perim (S.initial n)
  initialRange : ∀ n, range (S.initial n).1 = range (current n).1
  pathEndRange : ∀ n, range (S.pathEnd n).1 = range (S.initial (n + 1)).1
  source_cost_le : ∀ n,
    (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ e n (k + 1)
  composition_d1 : ∀ n t,
    2 * ((S.path n).m t / Real.sqrt (1 - (kh n) ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0)
        (rearKappa1 (kh n))
        (∫ s in (0 : ℝ)..(S.path n).T, (S.source n).m s) ≤ (S.source n).m t
  composition_d2 : ∀ n t,
    ((S.source n).Dd t +
        2 * ((S.path n).m t / Real.sqrt (1 - (kh n) ^ 2))) *
        GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0)
          (rearKappa1 (kh n))
          (∫ s in (0 : ℝ)..(S.path n).T, (S.source n).m s) ^ 2 +
      2 * ((S.path n).m t / Real.sqrt (1 - (kh n) ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod (S.source n) 0)
          (rearKappa1 (kh n)) (rearKappa2 (kh n))
          (∫ s in (0 : ℝ)..(S.path n).T, (S.source n).m s) ≤ (S.source n).m t

theorem GeometricCompositionInvariant.rearPeriod_zero_le_initialUpper
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    rearPeriod (S.source n) 0 ≤ C n := by
  rw [H.rearPeriod_zero_eq_initial_perim n]
  exact H.initialTube n |>.speed_ub 0

/-- A row family transports the reachable invariant definitionally. -/
def GeometricPresentedRowFamily.mappedInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (F : GeometricPresentedRowFamily S) :
    GeometricCompositionInvariant F.mappedColumn where
  slice n := (F.compositionAnalytic n).slice
  periodUpper_le n := F.mappedPeriodUpper_le n
  rearCurvature_le n := F.mappedRearCurvature_le n
  frontPeriodScaleOne n := F.mappedFrontPeriodScaleOne n
  spatial n := (F.compositionAnalytic n).spatial
  sidecars n := (F.compositionAnalytic n).sidecars
  terminalCurvature_nonnegative n :=
    (F.compositionAnalytic n).terminalCurvature_nonnegative
  terminalRange n := (F.compositionAnalytic n).terminalRange
  terminalFront_phase n := F.mappedTerminalFront_phase n
  terminalFront_eq_phase n := F.mappedTerminalFront_eq_phase n
  nextFront_zero n := F.mappedNextFront_zero n
  nextPeriod_zero n := F.mappedNextPeriod_zero n
  initialTube n := F.mappedInitialTube n
  initialOrdinaryTube n := by
    let R := F.row n
    refine ⟨R.terminalInput.physical.cq,
      R.terminalInput.physical.dlt, R.terminalInput.physical.cq_pos, ?_⟩
    change IsTubeMember R.terminalInput.physical.cq 0
      R.terminalInput.physical.dlt (F.mappedInitial n)
    rw [F.mappedInitial_eq_phase n]
    exact MarkedShift.isTubeMember_shiftData
      R.terminalInput.zero_floor_tube (F.mappedInitial_phase n)
  rearPeriod_zero_eq_initial_perim n :=
    F.mappedRearPeriod_zero_eq_initial_perim n
  initialRange n := F.mappedColumn.initial_range n
  pathEndRange n := F.mappedColumn.pathEndRange n
  source_cost_le n := F.mappedCost_le n
  composition_d1 n := (F.compositionAnalytic n).composition_d1
  composition_d2 n := (F.compositionAnalytic n).composition_d2

structure GeometricPresentedState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ) (c dlt : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : GeometricCorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt kh Qmax
  invariant : GeometricCompositionInvariant column

def GeometricPresentedState.next
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (X : GeometricPresentedState Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (F : GeometricPresentedRowFamily X.column) :
    GeometricPresentedState Q e P0 P1 khat G1 Cg C kh Qmax c dlt where
  current := fun n => (F.row n).presented
  depth := X.depth + 1
  column := F.mappedColumn
  invariant := F.mappedInvariant

structure GeometricPresentedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ) (c dlt : ℝ) where
  rows : ∀ {current k}
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax),
      GeometricCompositionInvariant S → GeometricPresentedRowFamily S

structure GeometricPresentedConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ) (c dlt : ℝ) where
  base : GeometricCorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax
  baseInvariant : GeometricCompositionInvariant base
  base_range : ∀ n, range (base.initial n).1 = range (Q n).1
  provider : GeometricPresentedProvider Q e P0 P1 khat G1 Cg C kh Qmax c dlt

def GeometricPresentedConstructionCore.state
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt) :
    ℕ → GeometricPresentedState Q e P0 P1 khat G1 Cg C kh Qmax c dlt
  | 0 =>
      { current := Q
        depth := 0
        column := F.base
        invariant := F.baseInvariant }
  | k + 1 =>
      let X := F.state k
      X.next (F.provider.rows X.column X.invariant)

def GeometricPresentedConstructionCore.rowFamilyAt
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (k : ℕ) : GeometricPresentedRowFamily (F.state k).column :=
  F.provider.rows (F.state k).column (F.state k).invariant

/-- The actual arclength-marked rear at a reachable depth. -/
def GeometricPresentedConstructionCore.markedGrid
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) : Data := (F.state k).column.initial n

@[simp] theorem GeometricPresentedConstructionCore.markedGrid_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n : ℕ) : F.markedGrid n 0 = F.base.initial n := rfl

theorem GeometricPresentedConstructionCore.markedGrid_zero_range
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n : ℕ) : range (F.markedGrid n 0).1 = range (Q n).1 :=
  F.base_range n

/-- Every reachable actual source-initial representative remains in its
fixed row tube, independently of recursive depth. -/
theorem GeometricPresentedConstructionCore.markedGrid_tube
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) : VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.markedGrid n k) :=
  (F.state k).invariant.initialTube n

/-- At every fixed depth, the next row of the actual rear grid is the
unit-tangent front represented by the current source path endpoint. -/
theorem GeometricPresentedConstructionCore.markedGrid_front_range
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) :
    range (F.markedGrid (n + 1) k).1 =
      range ((F.state k).column.pathEnd n).1 := by
  exact ((F.state k).invariant.pathEndRange n).symm

theorem GeometricPresentedConstructionCore.markedGrid_succ_range
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) :
    range (F.markedGrid n (k + 1)).1 =
      range ((F.rowFamilyAt k).row n).output.jets.rear.1 := by
  exact (F.rowFamilyAt k).mappedInitialRange n

/-- At positive depth the actual source-initial rear is the retained cyclic
phase of the preceding row's constant-speed terminal representative. -/
theorem GeometricPresentedConstructionCore.markedGrid_succ_eq_phase
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) :
    F.markedGrid n (k + 1) = MarkedShift.shiftData
      ((F.rowFamilyAt k).mappedInitial_phase n)
      ((F.rowFamilyAt k).row n).presented := by
  exact (F.rowFamilyAt k).mappedInitial_eq_phase n

/-- Every finite geometric grid edge is the parameter-invariant unit-tangent
edge dictated by the terminal physical carrier. -/
theorem GeometricPresentedConstructionCore.markedGrid_edge
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n k : ℕ) :
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (F.markedGrid (n + 1) k) (F.markedGrid n (k + 1)) := by
  let R := (F.rowFamilyAt k).row n
  let I := NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl
    R.presented
  have hcanonical : range (F.markedGrid (n + 1) k).1 =
      range (UnitTangent.unitTangentMap (ev R.presented)) :=
    (F.markedGrid_front_range n k).trans R.terminalInput.canonical_range
  have H : VariableMarkedTube.GeometricUnitTangentRangeEdge
      (F.markedGrid (n + 1) k) R.presented := by
    exact GaugeRearFamilyVariableTerminal.geometricRangeEdge_of_flowMarking
      R.terminalInput.physical.cq_pos I.lambda_pos
      R.terminalInput.zero_floor_tube I.marking
      (by simpa [I, NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl]
        using continuous_id)
      (by simpa [I, NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl]
        using strictMono_id)
      I.psi_zero hcanonical
  rw [F.markedGrid_succ_eq_phase n k]
  unfold VariableMarkedTube.GeometricUnitTangentRangeEdge at H ⊢
  rw [range_geometricUnitTangent_shiftData]
  exact H

end FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
