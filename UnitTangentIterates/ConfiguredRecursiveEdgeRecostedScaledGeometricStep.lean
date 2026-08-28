import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedGeometricState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledPreCarrier

/-! # One multiplier-aware recosted geometric step -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedScaledGeometricStep

open ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  GaugeMarkedDataOfRearFamily

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}

structure Regularity
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) (n : ℕ) where
  eta_continuous : Continuous
    (uncurry (output X.invariant n).chosen.Delta.eta)
  eta1_continuous : Continuous
    (uncurry (output X.invariant n).chosen.c2.eta1)
  eta2_continuous : Continuous
    (uncurry (output X.invariant n).chosen.c2.eta2)
  time_one : (output X.invariant n).chosen.Delta.T = 1

def core
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) (n : ℕ)
    (R : Regularity X n) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core (X.stage n) where
  geometric := X.geometricInput n
  eta_continuous := R.eta_continuous
  eta1_continuous := R.eta1_continuous
  eta2_continuous := R.eta2_continuous
  time_one := R.time_one

/-- Configured ordinary-flow bounds select the canonical row. -/
structure RowBounds
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) where
  P1_le : ∀ n, GaugeFlowDerivCost.costP1
    (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (X.column.source n) 0) kappaHat
      (∫ t in (0 : ℝ)..(X.column.path n).T, (X.column.source n).m t) ≤ P1 n
  G1_le : ∀ n, GaugeFlowDerivCost.costG1
    (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (X.column.source n) 0) kappaHat (rearKappa2 kappa)
      (∫ t in (0 : ℝ)..(X.column.path n).T, (X.column.source n).m t) ≤ G1 n
  Cg_le : ∀ n,
    kappaHat * GaugeFlowDerivCost.costG1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
          (X.column.source n) 0) kappaHat (rearKappa2 kappa)
          (∫ t in (0 : ℝ)..(X.column.path n).T, (X.column.source n).m t) +
      rearKappa2 kappa * GaugeFlowDerivCost.costP1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
          (X.column.source n) 0) kappaHat
          (∫ t in (0 : ℝ)..(X.column.path n).T, (X.column.source n).m t) ^ 2 ≤ Cg n

namespace RowBounds

noncomputable def row
    (B : RowBounds X) (n : ℕ) :
    GeometricPresentedRowSelection (n := n) X.column :=
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.row
    X.invariant n (B.P1_le n) (B.G1_le n) (B.Cg_le n)

@[simp] theorem row_output (B : RowBounds X) (n : ℕ) :
    (B.row n).output = output X.invariant n := rfl

end RowBounds

/-- Exact facts not encoded by the scalar multiplier itself.  Every analytic
carrier and recursive source is constructed from `scaled`; this record only
retains phase, tube, and configured ceiling consequences. -/
structure StepInput
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) where
  rowBounds : RowBounds X
  regularity : ∀ n, Regularity X n
  scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
    (P0 (n + (X.depth + 1))) kappa kappaHat (Qmax (n + (X.depth + 1)))
  recursiveFacts : ∀ n, Input.RecursiveFacts (scaled n)
  mappedInitial : ℕ → Data
  mappedInitial_eq : ∀ n u, (mappedInitial n).1 u =
    RearOwnArclength.rearOwn (Input.source (scaled n)).F
      (Input.source (scaled n)).Theta (Input.source (scaled n)).delta
      (Input.source (scaled n)).sf 0
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (Input.source (scaled n)) 0 * u)
  mappedInitial_phase : ℕ → ℝ
  mappedInitial_eq_phase : ∀ n, mappedInitial n =
    MarkedShift.shiftData (mappedInitial_phase n) (rowBounds.row n).presented
  mappedInitialRange : ∀ n,
    range (mappedInitial n).1 = range (rowBounds.row n).output.jets.rear.1
  mappedTerminalFront_phase : ℕ → ℝ
  mappedTerminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (Input.source (scaled n)) = MarkedShift.shiftData
        (mappedTerminalFront_phase n) (mappedInitial (n + 1))
  mappedNextFront_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
      (Input.source (scaled (n + 1))) 0 = ev (mappedInitial (n + 1))
  mappedNextPeriod_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (Input.source (scaled (n + 1))) 0 = perim (mappedInitial (n + 1))
  mappedInitialTube : ∀ n, VariableMarkedTube.IsVariableTubeMember
    c (C n) 0 dlt (mappedInitial n)
  mappedRearPeriod_zero_eq_initial_perim : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (Input.source (scaled n)) 0 = perim (mappedInitial n)
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(core X (n + 1) (regularity (n + 1))).path.T,
      (Input.source (scaled n)).m t) ≤ e n ((X.depth + 1) + 1)
  mappedPeriodUpper_le : ∀ n,
    (Input.slice (scaled n)).periodUpper ≤ P1 n
  mappedRearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (Input.source (scaled n)) t s| ≤ kappa
  mappedFrontPeriodScaleOne : ∀ n t,
    1 ≤ Real.sqrt (1 - kappa ^ 2) * (Input.source (scaled n)).P t
  mappedPeriod_zero_le_Qmax : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (Input.source (scaled n)) 0 ≤ Qmax (n + (X.depth + 1))

namespace StepInput

variable {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

def family
    (H : StepInput X) : RecostedGeometricPresentedRowFamily X.column where
  row := H.rowBounds.row
  carrier n := (core X (n + 1) (H.regularity (n + 1))).path
  recursive n := Input.recursive (H.scaled n) (H.recursiveFacts n)
  mappedInitial := H.mappedInitial
  mappedInitial_eq := H.mappedInitial_eq
  mappedInitial_phase := H.mappedInitial_phase
  mappedInitial_eq_phase := H.mappedInitial_eq_phase
  mappedInitialRange := H.mappedInitialRange
  mappedTerminalFront_phase := H.mappedTerminalFront_phase
  mappedTerminalFront_eq_phase := H.mappedTerminalFront_eq_phase
  mappedNextFront_zero := H.mappedNextFront_zero
  mappedNextPeriod_zero := H.mappedNextPeriod_zero
  mappedInitialTube := H.mappedInitialTube
  mappedRearPeriod_zero_eq_initial_perim :=
    H.mappedRearPeriod_zero_eq_initial_perim
  mappedCost_le := H.mappedCost_le
  mappedPeriodUpper_le := H.mappedPeriodUpper_le
  mappedRearCurvature_le := H.mappedRearCurvature_le
  mappedFrontPeriodScaleOne := H.mappedFrontPeriodScaleOne
  mapped_d1 n := Input.composition_d1 (H.scaled n)
    (H.mappedPeriod_zero_le_Qmax n)
  mapped_d2 n := Input.composition_d2 (H.scaled n)
    (H.mappedPeriod_zero_le_Qmax n)

def next (H : StepInput X) :
    State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa :=
  X.next H.family

end StepInput

end ConfiguredRecursiveEdgeRecostedScaledGeometricStep
