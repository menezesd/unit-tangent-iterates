import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

/-!
# Recost-carrier geometric presented recursion

This is the sound mapped-column interface for a recursive source on a
canonical recost of the chosen path.  Unlike the legacy row family, the
carrier path is explicit.  The multiplier-aware exact source supplies the
two application inequalities required by the following presented row.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
  {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    kh Qmax}

/-- A selected row family whose next exact sources live on explicit recosted
carriers.  All fields are exact outputs of the row and multiplier-aware
source constructors. -/
structure RecostedGeometricPresentedRowFamily
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) where
  row : ∀ n, GeometricPresentedRowSelection (n := n) S
  carrier : ∀ n, NormalPath (S.initial (n + 1)) (row (n + 1)).output.jets.rear
  recursive : ∀ n, RecursiveAnalyticSuccessor (carrier n) (S.source (n + 1))
    (P0 (n + (k + 1))) (kh n) (khat n) (Qmax (n + (k + 1)))
  mappedInitial : ∀ n, Data
  mappedInitial_eq : ∀ n u, (mappedInitial n).1 u =
    RearOwnArclength.rearOwn (recursive n).source.F
      (recursive n).source.Theta (recursive n).source.delta
      (recursive n).source.sf 0 (rearPeriod (recursive n).source 0 * u)
  mappedInitial_phase : ∀ n, ℝ
  mappedInitial_eq_phase : ∀ n, mappedInitial n =
    MarkedShift.shiftData (mappedInitial_phase n) (row n).presented
  mappedInitialRange : ∀ n,
    range (mappedInitial n).1 = range (row n).output.jets.rear.1
  mappedTerminalFront_phase : ∀ n, ℝ
  mappedTerminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (recursive n).source = MarkedShift.shiftData
        (mappedTerminalFront_phase n) (mappedInitial (n + 1))
  mappedNextFront_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
      (recursive (n + 1)).source 0 = ev (mappedInitial (n + 1))
  mappedNextPeriod_zero : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (recursive (n + 1)).source 0 = perim (mappedInitial (n + 1))
  mappedInitialTube : ∀ n, VariableMarkedTube.IsVariableTubeMember
    c (C n) 0 dlt (mappedInitial n)
  mappedRearPeriod_zero_eq_initial_perim : ∀ n,
    rearPeriod (recursive n).source 0 = perim (mappedInitial n)
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(carrier n).T, (recursive n).source.m t) ≤
      e n ((k + 1) + 1)
  mappedPeriodUpper_le : ∀ n, (recursive n).slice.periodUpper ≤ P1 n
  mappedRearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (recursive n).source t s| ≤ kh n
  mappedFrontPeriodScaleOne : ∀ n t,
    1 ≤ Real.sqrt (1 - (kh n) ^ 2) * (recursive n).source.P t
  mapped_d1 : ∀ n t,
    2 * ((carrier n).m t / Real.sqrt (1 - (kh n) ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod (recursive n).source 0)
        (rearKappa1 (kh n))
        (∫ s in (0 : ℝ)..(carrier n).T, (recursive n).source.m s) ≤
      (recursive n).source.m t
  mapped_d2 : ∀ n t,
    ((recursive n).source.Dd t +
        2 * ((carrier n).m t / Real.sqrt (1 - (kh n) ^ 2))) *
        GaugeFlowDerivCost.costP1 (rearPeriod (recursive n).source 0)
          (rearKappa1 (kh n))
          (∫ s in (0 : ℝ)..(carrier n).T, (recursive n).source.m s) ^ 2 +
      2 * ((carrier n).m t / Real.sqrt (1 - (kh n) ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod (recursive n).source 0)
          (rearKappa1 (kh n)) (rearKappa2 (kh n))
          (∫ s in (0 : ℝ)..(carrier n).T, (recursive n).source.m s) ≤
      (recursive n).source.m t

namespace RecostedGeometricPresentedRowFamily

/-- The mapped column uses the recosted carrier from row `n+1`. -/
def mappedColumn (F : RecostedGeometricPresentedRowFamily S) :
    GeometricCorrelatedColumn Q (fun n => (F.row n).presented)
      e (k + 1) P0 P1 khat G1 Cg C c dlt kh Qmax where
  pathStart n := S.initial (n + 1)
  pathEnd n := (F.row (n + 1)).output.jets.rear
  path := F.carrier
  source n := (F.recursive n).source
  initial := F.mappedInitial
  initial_eq := F.mappedInitial_eq
  initial_range n := by
    rw [F.mappedInitial_eq_phase n]
    exact range_shiftData _ _
  pathEndRange n := (F.mappedInitialRange (n + 1)).symm

/-- Every invariant field is retained by the exact recursive source or the
phase-aware mapped family. -/
def mappedInvariant (F : RecostedGeometricPresentedRowFamily S) :
    GeometricCompositionInvariant F.mappedColumn where
  slice n := (F.recursive n).slice
  periodUpper_le n := F.mappedPeriodUpper_le n
  rearCurvature_le n := F.mappedRearCurvature_le n
  frontPeriodScaleOne n := F.mappedFrontPeriodScaleOne n
  spatial n := (F.recursive n).spatial
  sidecars n := (F.recursive n).sidecars
  terminalCurvature_nonnegative n :=
    (F.recursive n).terminalCurvature_nonnegative
  terminalRange n := (F.recursive n).terminalRange
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
    exact MarkedShift.isTubeMember_shiftData R.terminalInput.zero_floor_tube
      (F.mappedInitial_phase n)
  rearPeriod_zero_eq_initial_perim n :=
    F.mappedRearPeriod_zero_eq_initial_perim n
  initialRange n := F.mappedColumn.initial_range n
  pathEndRange n := F.mappedColumn.pathEndRange n
  source_cost_le n := F.mappedCost_le n
  composition_d1 n := F.mapped_d1 n
  composition_d2 n := F.mapped_d2 n

end RecostedGeometricPresentedRowFamily

end FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion
