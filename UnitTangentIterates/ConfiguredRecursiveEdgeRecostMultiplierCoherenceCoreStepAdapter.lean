import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricCoherence
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierOuterLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricGeometry
import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedCapstone

/-!
# Callback-free completion of a global coherence core

The raw metric controls the current datum against the unshifted canonical
endpoint.  The configured row budget is therefore applied to that canonical
endpoint first; only afterwards is the resulting variable-tube certificate
transported through `mappedInitial_eq_phase`.  This avoids the false stronger
requirement that a cyclic phase shift be small in the marked metric.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierCoherenceCoreStepAdapter

open ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierOuterLayer
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledGeometricCoherence
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg Qmax : ℕ → ℝ} {kappaHat : ℝ}
  {X : State Q e P0 P1 G1 Cg (upper R) Qmax kappaHat
    (R.data.Hs 0)
    (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}

variable
  {rowBounds : RowBounds X}
  {regularity : ∀ n, Regularity X n}
  {scaled : ∀ n, ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input
    (core X (n + 1) (regularity (n + 1)))
    (P0 (n + (X.depth + 1)))
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh kappaHat
    (Qmax (n + (X.depth + 1)))}

/-- The canonical raw metric package selected by the row bounds. -/
noncomputable def rawMetric (n : ℕ) :
    RawMetricGeometry.Bounded (X.geometricInput n) :=
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry.ofCanonicalRow X.invariant n
    (rowBounds.P1_le n) (rowBounds.G1_le n) (rowBounds.Cg_le n)

/-- All scalar data needed to complete an exact `CoherenceCore` to the public
global `StepInput`.  No tube callback occurs: `mappedInitialTube` below is a
theorem of this record and the configured row budget. -/
structure CoreStep : Prop where
  prefixDistance : ∀ n,
    dist (base R n) (X.stage n).displayed ≤ accumulated R n X.depth
  model_tube : ∀ n, IsTubeMember
    (2 * R.data.Hs 0) 0
    (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n)
  model_acc : ∀ n u, ‖(base R n).2.2 u‖ ≤
    ConfiguredInductiveTubeBudget.accBound R.data.model n
  edgeBudget_le_error : ∀ n,
    (rawMetric (R := R) (rowBounds := rowBounds) n).edgeBudget ≤
      R.error n X.depth
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..(core X (n + 1) (regularity (n + 1))).path.T,
      (scaled n).source.m t) ≤ e n ((X.depth + 1) + 1)
  mappedPeriodUpper_le : ∀ n, (scaled n).slice.periodUpper ≤ P1 n
  mappedRearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (scaled n).source t s| ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
  mappedFrontPeriodScaleOne : ∀ n t,
    1 ≤ Real.sqrt
      (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
        (scaled n).source.P t
  mappedPeriod_zero_le_Qmax : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (scaled n).source 0 ≤ Qmax (n + (X.depth + 1))

namespace CoreStep

/-- Raw metric control of the unshifted canonical endpoint. -/
theorem canonical_stepDistance
    (S : @CoreStep J O R Q e P0 P1 G1 Cg Qmax kappaHat X
      rowBounds regularity scaled) (n : ℕ) :
    dist (X.stage n).displayed (rowBounds.row n).presented ≤
      R.error n X.depth :=
  (rawMetric (R := R) (rowBounds := rowBounds) n).dist_displayed_base_le.trans
    (S.edgeBudget_le_error n)

/-- The configured tube is first proved for the unshifted canonical endpoint.
-/
theorem canonicalTube
    (S : @CoreStep J O R Q e P0 P1 G1 Cg Qmax kappaHat X
      rowBounds regularity scaled) (n : ℕ) :
    VariableMarkedTube.IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (rowBounds.row n).presented := by
  let A := rowBounds.row n
  let T := A.terminalInput.zero_floor_tube
  apply ConfiguredRecursiveEdgeRecostedOuterTubeStep.variableTube_next_of_rowBudget
    (rowBudget R) n (S.model_tube n) (S.model_acc n)
    T.hasDerivAt_curve T.hasDerivAt_vel T.periodic
  · exact fun u ↦ by simpa using T.curv_lb u
  · exact S.prefixDistance n
  · exact canonical_stepDistance R S n
  · exact error_prefix_add_step_le_radius R n X.depth

/-- Phase transport turns the canonical tube into the exact mapped-initial
tube required by `Coherence.toStepInput`. -/
theorem mappedInitialTube
    (S : @CoreStep J O R Q e P0 P1 G1 Cg Qmax kappaHat X
      rowBounds regularity scaled)
    (H : CoherenceCore X rowBounds regularity scaled) (n : ℕ) :
    VariableMarkedTube.IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (H.mappedInitial n) := by
  rw [H.mappedInitial_eq_phase n]
  exact ConfiguredRecursiveEdgeGeometricPresentedCapstone.isVariableTubeMember_shiftData
    (canonicalTube R S n) (H.mappedInitial_phase n)

/-- Callback-free completion of the exact core to a global step input. -/
noncomputable def toStepInput
    (S : @CoreStep J O R Q e P0 P1 G1 Cg Qmax kappaHat X
      rowBounds regularity scaled)
    (H : CoherenceCore X rowBounds regularity scaled) : StepInput X :=
  Coherence.toStepInput H (mappedInitialTube R S H) S.mappedCost_le
    S.mappedPeriodUpper_le S.mappedRearCurvature_le
    S.mappedFrontPeriodScaleOne S.mappedPeriod_zero_le_Qmax

end CoreStep

end ConfiguredRecursiveEdgeRecostMultiplierCoherenceCoreStepAdapter
