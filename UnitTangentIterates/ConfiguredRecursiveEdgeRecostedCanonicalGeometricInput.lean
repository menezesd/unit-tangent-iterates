import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRowState
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

/-!
# Canonical geometric input for a recost-allowance column

The canonical presented-row construction is parametric in its error table.
This adapter exposes its theorem-produced terminal and output as an actual
pullback stage.  In particular, callers may instantiate `e` with the
recosted-source allowance instead of the legacy composition error.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ} {kappa kappaHat c dlt : ℝ}
  {S : GeometricCorrelatedColumn Q current e k P0 P1
    (fun _ ↦ kappaHat) G1 Cg C c dlt (fun _ ↦ kappa) Qmax}

/-- The actual stage underlying row `n` of a reachable geometric column. -/
noncomputable def stage (H : GeometricCompositionInvariant S) (n : ℕ) :
    Stage P0 (fun _ ↦ kappa) (fun _ ↦ kappaHat) Qmax (n + k) where
  start := S.pathStart n
  rear := S.pathEnd n
  Gamma := S.path n
  source := S.source n
  applied := applied H n
  displayed := S.initial n

/-- The canonical row supplies the complete geometric input for its actual
stage.  Its bound is exactly the caller-selected table entry `e n (k+1)`. -/
noncomputable def geometricInput
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    GeometricInput (stage H n) where
  base := (geometry H n).presented
  bound := e n (k + 1)
  terminal := terminalInput H n
  output := output H n

@[simp] theorem stage_displayed
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    (stage H n).displayed = S.initial n := rfl

@[simp] theorem geometricInput_base
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    (geometricInput H n).base = (geometry H n).presented := rfl

@[simp] theorem geometricInput_bound
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    (geometricInput H n).bound = e n (k + 1) := rfl

@[simp] theorem geometricInput_output
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    (geometricInput H n).output = output H n := rfl

end ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

