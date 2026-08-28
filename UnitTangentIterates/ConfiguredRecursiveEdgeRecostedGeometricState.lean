import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

/-! # Constant-profile state for the recosted geometric recursion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedGeometricState

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion

/-- The configured curvature profiles are constant; `P0` and `Qmax` retain
the diagonal index.  No root shift is built into this structure. -/
structure State
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 G1 Cg C Qmax : ℕ → ℝ)
    (kappaHat c dlt kappa : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : GeometricCorrelatedColumn Q current e depth P0 P1
    (fun _ => kappaHat) G1 Cg C c dlt (fun _ => kappa) Qmax
  invariant : GeometricCompositionInvariant column

namespace State

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}

def next
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa)
    (F : RecostedGeometricPresentedRowFamily X.column) :
    State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa where
  current := fun n => (F.row n).presented
  depth := X.depth + 1
  column := F.mappedColumn
  invariant := F.mappedInvariant

/-- Actual stage at the diagonal index `n + depth`. -/
def stage
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) (n : ℕ) :
    Stage P0 (fun _ => kappa) (fun _ => kappaHat) Qmax (n + X.depth) where
  start := X.column.pathStart n
  rear := X.column.pathEnd n
  Gamma := X.column.path n
  source := X.column.source n
  applied := applied X.invariant n
  displayed := X.column.initial n

def geometricInput
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) (n : ℕ) :
    GeometricInput (X.stage n) where
  base := (geometry X.invariant n).presented
  bound := e n (X.depth + 1)
  terminal := terminalInput X.invariant n
  output := output X.invariant n

@[simp] theorem stage_displayed
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa) (n : ℕ) :
    (X.stage n).displayed = X.column.initial n := rfl

@[simp] theorem next_stage_displayed
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa)
    (F : RecostedGeometricPresentedRowFamily X.column) (n : ℕ) :
    ((X.next F).stage n).displayed = F.mappedInitial n := rfl

end State

end ConfiguredRecursiveEdgeRecostedGeometricState
