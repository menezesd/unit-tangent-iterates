import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

/-!
# Relabeling the geometric invariant by the truthful recost allowance

The error table is phantom in `GeometricCorrelatedColumn`; only the source
cost field of `GeometricCompositionInvariant` depends on it.  Thus the whole
geometric/phase/tube invariant transports unchanged once the truthful source
mass inequality is supplied.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedCompositionInvariant

open ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

def recostErrorTable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (n depth : ℕ) : ℝ :=
  recostSourceAllowance D E C0 C1 C2 (n + (depth - 1))

@[simp] theorem recostErrorTable_succ
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (n k : ℕ) :
    recostErrorTable D E C0 C1 C2 n (k + 1) =
      recostSourceAllowance D E C0 C1 C2 (n + k) := by
  simp [recostErrorTable]

variable {Q current : ℕ → Data} {e e' : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

/-- Change only the phantom error table of a geometric column. -/
def relabelColumn
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) :
    GeometricCorrelatedColumn Q current e' k P0 P1 khat G1 Cg C c dlt
      kh Qmax where
  pathStart := S.pathStart
  pathEnd := S.pathEnd
  path := S.path
  source := S.source
  initial := S.initial
  initial_eq := S.initial_eq
  initial_range := S.initial_range
  pathEndRange := S.pathEndRange

/-- Preserve the complete invariant while replacing its one quantitative
source-cost field. -/
def relabelInvariant
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax)
    (H : GeometricCompositionInvariant S)
    (hcost : ∀ n,
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ e' n (k + 1)) :
    GeometricCompositionInvariant (relabelColumn (e' := e') S) where
  slice := H.slice
  periodUpper_le := H.periodUpper_le
  rearCurvature_le := H.rearCurvature_le
  frontPeriodScaleOne := H.frontPeriodScaleOne
  spatial := H.spatial
  sidecars := H.sidecars
  terminalCurvature_nonnegative := H.terminalCurvature_nonnegative
  terminalRange := H.terminalRange
  terminalFront_phase := H.terminalFront_phase
  terminalFront_eq_phase := H.terminalFront_eq_phase
  nextFront_zero := H.nextFront_zero
  nextPeriod_zero := H.nextPeriod_zero
  initialTube := H.initialTube
  initialOrdinaryTube := H.initialOrdinaryTube
  rearPeriod_zero_eq_initial_perim := H.rearPeriod_zero_eq_initial_perim
  initialRange := H.initialRange
  pathEndRange := H.pathEndRange
  source_cost_le := hcost
  composition_d1 := H.composition_d1
  composition_d2 := H.composition_d2

/-- Specialize an existing reachable invariant to the diagonal recost-source
allowance. -/
def withRecostAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data) (E C0 C1 C2 : ℝ)
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax)
    (H : GeometricCompositionInvariant S)
    (hcost : ∀ n,
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤
        recostSourceAllowance D E C0 C1 C2 (n + k)) :
    GeometricCompositionInvariant
      (relabelColumn
        (e' := recostErrorTable D E C0 C1 C2) S) :=
  relabelInvariant S H (by
    intro n
    simpa using hcost n)

end ConfiguredRecursiveEdgeRecostedCompositionInvariant

