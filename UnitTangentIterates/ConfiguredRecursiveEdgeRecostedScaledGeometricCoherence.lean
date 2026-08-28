import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep

/-! # Exact coherence for one multiplier-aware recosted geometric step

This record separates the theorem-produced phase and source identities from
the five scalar inequalities used by the configured diagonal.  In particular,
the constructor back to `StepInput` cannot accidentally treat cost or period
ceilings as geometric coherence.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedScaledGeometricCoherence

open ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}

/-- The canonical displayed representative of a direct recost source is its
time-zero arclength-marked selected rear. -/
def canonicalMappedInitial
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {regularity : ∀ n, Regularity X n}
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) (n : ℕ) : Data :=
  (Input.source (scaled n)).selectedRearData 0

theorem canonicalMappedInitial_eq
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {regularity : ∀ n, Regularity X n}
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) (n : ℕ) (u : ℝ) :
    (canonicalMappedInitial scaled n).1 u =
      RearOwnArclength.rearOwn (Input.source (scaled n)).F
        (Input.source (scaled n)).Theta (Input.source (scaled n)).delta
        (Input.source (scaled n)).sf 0
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
          (Input.source (scaled n)) 0 * u) := rfl

theorem canonicalMappedNextFront_zero
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {regularity : ∀ n, Regularity X n}
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
      (Input.source (scaled (n + 1))) 0 =
        ev (canonicalMappedInitial scaled (n + 1)) := by
  funext x
  exact (FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.ev_selectedRearData
    (Input.source (scaled (n + 1))) 0 x).symm

theorem canonicalMappedNextPeriod_zero
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {regularity : ∀ n, Regularity X n}
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (Input.source (scaled (n + 1))) 0 =
        perim (canonicalMappedInitial scaled (n + 1)) := by
  exact (FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearData_perim
    (Input.source (scaled (n + 1))) 0).symm

theorem canonicalMappedRearPeriod_zero_eq_initial_perim
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {regularity : ∀ n, Regularity X n}
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (Input.source (scaled n)) 0 =
        perim (canonicalMappedInitial scaled n) := by
  exact (FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearData_perim
    (Input.source (scaled n)) 0).symm

/-- Transport the ordinary terminal tube to the canonical mapped initial.
This isolates the only three scalar comparisons required to place a local
terminal presentation in a fixed common variable tube. -/
theorem canonicalMappedInitialTube_of_local
    {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
    {rowBounds : RowBounds X}
    {regularity : ∀ n, Regularity X n}
    {scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))}
    (n : ℕ) (phase : ℝ)
    (hphase : canonicalMappedInitial scaled n =
      MarkedShift.shiftData phase (rowBounds.row n).presented)
    (hc : c ≤ (rowBounds.row n).terminalInput.physical.cq)
    (hC : perim (rowBounds.row n).presented ≤ C n)
    (hdlt : dlt ≤ (rowBounds.row n).terminalInput.physical.dlt) :
    VariableMarkedTube.IsVariableTubeMember c (C n) 0 dlt
      (canonicalMappedInitial scaled n) := by
  rw [hphase]
  let R := rowBounds.row n
  let H := MarkedShift.isTubeMember_shiftData R.terminalInput.zero_floor_tube phase
  refine
    { hasDerivAt_curve := H.hasDerivAt_curve
      hasDerivAt_vel := H.hasDerivAt_vel
      periodic := H.periodic
      speed_lb := fun u ↦ hc.trans (H.speed_lb u)
      speed_ub := fun u ↦ ?_
      curv_lb := H.curv_lb
      chord := fun u hu v hv ↦ ?_ }
  · rw [MarkedSpace.norm_vel_eq_perim H u,
      SelectedInverseShiftEquivariance.perim_shiftData
        R.terminalInput.zero_floor_tube phase]
    exact hC
  · exact (mul_le_mul_of_nonneg_right hdlt (cyc_nonneg hu hv)).trans
      (H.chord u hu v hv)

/-- The exact, non-scalar part of a recosted geometric step. -/
structure CoherenceCore
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa)
    (rowBounds : RowBounds X)
    (regularity : ∀ n, Regularity X n)
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) where
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
  mappedRearPeriod_zero_eq_initial_perim : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (Input.source (scaled n)) 0 = perim (mappedInitial n)

/-- Backwards-compatible short name for the exact coherence core.  The common
tube is intentionally supplied only after the outer distance induction. -/
abbrev Coherence
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa)
    (rowBounds : RowBounds X)
    (regularity : ∀ n, Regularity X n)
    (scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
      (P0 (n + (X.depth + 1))) kappa kappaHat
      (Qmax (n + (X.depth + 1)))) :=
  CoherenceCore X rowBounds regularity scaled

namespace Coherence

variable
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}
  {rowBounds : RowBounds X}
  {regularity : ∀ n, Regularity X n}
  {scaled : ∀ n, Input (core X (n + 1) (regularity (n + 1)))
    (P0 (n + (X.depth + 1))) kappa kappaHat
    (Qmax (n + (X.depth + 1)))}

/-- Add only the five scalar/row ceilings to recover the public step input. -/
def toStepInput
    (H : Coherence X rowBounds regularity scaled)
    (mappedInitialTube : ∀ n, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (H.mappedInitial n))
    (mappedCost_le : ∀ n,
      (∫ t in (0 : ℝ)..(core X (n + 1) (regularity (n + 1))).path.T,
        (Input.source (scaled n)).m t) ≤ e n ((X.depth + 1) + 1))
    (mappedPeriodUpper_le : ∀ n, (Input.slice (scaled n)).periodUpper ≤ P1 n)
    (mappedRearCurvature_le : ∀ n t s,
      |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
        (Input.source (scaled n)) t s| ≤ kappa)
    (mappedFrontPeriodScaleOne : ∀ n t,
      1 ≤ Real.sqrt (1 - kappa ^ 2) * (Input.source (scaled n)).P t)
    (mappedPeriod_zero_le_Qmax : ∀ n,
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (Input.source (scaled n)) 0 ≤ Qmax (n + (X.depth + 1))) :
    StepInput X where
  rowBounds := rowBounds
  regularity := regularity
  scaled := scaled
  recursiveFacts := H.recursiveFacts
  mappedInitial := H.mappedInitial
  mappedInitial_eq := H.mappedInitial_eq
  mappedInitial_phase := H.mappedInitial_phase
  mappedInitial_eq_phase := H.mappedInitial_eq_phase
  mappedInitialRange := H.mappedInitialRange
  mappedTerminalFront_phase := H.mappedTerminalFront_phase
  mappedTerminalFront_eq_phase := H.mappedTerminalFront_eq_phase
  mappedNextFront_zero := H.mappedNextFront_zero
  mappedNextPeriod_zero := H.mappedNextPeriod_zero
  mappedInitialTube := mappedInitialTube
  mappedRearPeriod_zero_eq_initial_perim := H.mappedRearPeriod_zero_eq_initial_perim
  mappedCost_le := mappedCost_le
  mappedPeriodUpper_le := mappedPeriodUpper_le
  mappedRearCurvature_le := mappedRearCurvature_le
  mappedFrontPeriodScaleOne := mappedFrontPeriodScaleOne
  mappedPeriod_zero_le_Qmax := mappedPeriod_zero_le_Qmax

end Coherence

end ConfiguredRecursiveEdgeRecostedScaledGeometricCoherence
