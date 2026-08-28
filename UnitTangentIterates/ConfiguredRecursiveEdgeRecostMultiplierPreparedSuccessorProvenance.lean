import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure

/-!
# Prepared successor provenance for the intrinsic multiplier recursion

The global geometric state and the intrinsic diagonal nodes use intentionally
different dependent profile/index types.  Their stages therefore align by
`HEq`, not by an invalid equality after erasing profile parameters.  Once this
single alignment is retained, automatic successor regularity supplies the
canonical pre-carrier on the geometric side and `HEq` transports it to the
intrinsic successor layer.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierPreparedSuccessorProvenance

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance
  ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

/-- Minimal source-side readiness retained at a reached intrinsic layer.  The
remaining scalar, raw-metric, and phase fields can be attached by the existing
analytic/coherent readiness constructors. -/
structure CoreReadiness {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) where
  pre : ∀ n, Core (S n).stage

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

variable {k : ℕ} {S : ℕ → Node} {L : Layer R k S}

/-- Exact dependent-stage alignment between a geometric multiplier successor
and the corresponding intrinsic diagonal successor. -/
structure SuccessorStageAlignment
    (H : StepInput X) (I : InputData R L) where
  stage_heq : ∀ n, HEq (H.next.stage n) ((I.step).next n).stage
  /-- The intrinsic pre-carrier must be constructed natively.  `Core` also
  depends on the hidden profile functions and depth index, so it cannot be
  transported from `stage_heq` alone. -/
  intrinsicPre : ∀ n, Core ((I.step).next n).stage
  pre_heq : ∀ n, HEq
    (ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance.successorPre
      H (regularity_next H) n)
    (intrinsicPre n)

/-- All theorem-produced provenance needed to begin analytic readiness at the
successor intrinsic layer.  No error-table, phase, or raw-metric callback is
stored here. -/
structure PreparedSuccessor
    (H : StepInput X) (I : InputData R L) where
  alignment : SuccessorStageAlignment R H I
  regularity : ∀ n, Regularity H.next n
  geometricPre : ∀ n, Core (H.next.stage n)
  intrinsicPre : ∀ n, Core ((I.step).next n).stage
  pre_heq : ∀ n, HEq (geometricPre n) (intrinsicPre n)

namespace PreparedSuccessor

/-- Canonical preparation of the successor.  Joint chosen-path regularity and
all geometric pre-carrier fields are theorem-produced; only dependent stage
alignment is supplied by the rowwise bridge. -/
noncomputable def ofAlignment
    (H : StepInput X) (I : InputData R L)
    (A : SuccessorStageAlignment R H I) : PreparedSuccessor R H I where
  alignment := A
  regularity := regularity_next H
  geometricPre n :=
    ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance.successorPre
      H (regularity_next H) n
  intrinsicPre := A.intrinsicPre
  pre_heq := A.pre_heq

/-- Minimal pre-carrier readiness for the already-normalized intrinsic
successor layer. -/
noncomputable def coreReadiness
    {H : StepInput X} {I : InputData R L}
    (P : PreparedSuccessor R H I) : CoreReadiness R I.nextLayer where
  pre := P.intrinsicPre

/-- The retained successor column is exactly the mapped row family chosen by
the input step. -/
theorem column_eq_mapped
    {H : StepInput X} {I : InputData R L}
    (P : PreparedSuccessor R H I) :
    H.next.column = H.family.mappedColumn := by
  rfl

/-- The retained successor invariant is exactly the mapped invariant of the
same family. -/
theorem invariant_eq_mapped
    {H : StepInput X} {I : InputData R L}
    (P : PreparedSuccessor R H I) :
    H.next.invariant = H.family.mappedInvariant := by
  rfl

end PreparedSuccessor

end ConfiguredRecursiveEdgeRecostMultiplierPreparedSuccessorProvenance
