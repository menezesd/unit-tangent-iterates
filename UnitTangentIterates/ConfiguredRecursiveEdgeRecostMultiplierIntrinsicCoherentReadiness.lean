import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility

/-!
# Coherent analytic readiness for one intrinsic multiplier layer

The multiplier source itself determines the next displayed datum: it is the
selected rear at time zero.  Thus the terminal reference for row `n` is the
actual next-row displayed datum, not an independently chosen representative.
The cross-row phase theorem composes the terminal gauge phase with the inverse
of the next initial phase and supplies the exact terminal-front equality.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicCoherentReadiness

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  VariableMarkedTube

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

/-- The two genuine cross-row facts not contained in source-side readiness.
The next displayed datum is not a field: it is canonically the multiplier
source's selected rear at time zero. -/
structure CoherentReadiness {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) extends Readiness R L where
  initialPhase : ℕ → ℝ
  selectedInitial_eq_phase : ∀ n,
    (toReadiness.toRawReadiness.globalScaled R n).source.selectedRearData 0 =
      MarkedShift.shiftData (initialPhase n) (pre n).geometric.base
  rawDiagonalRangeEdge : ∀ n,
    GeometricUnitTangentRangeEdge (S (n + 1)).stage.displayed
      (pre n).geometric.base

namespace CoherentReadiness

noncomputable def canonicalNextDisplayed
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) (n : ℕ) : Data :=
  (H.toReadiness.toRawReadiness.globalScaled R n).source.selectedRearData 0

noncomputable def terminalPhase
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) (n : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
      (H.toReadiness.toRawReadiness.globalScaled R n).selected
      (H.toReadiness.toRawReadiness.globalScaled R n).gauge.q
      (H.pre (n + 1)).geometric.output.chosen.Delta.T /
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (S (n + 1)).stage.source
      (H.pre (n + 1)).geometric.output.chosen.Delta.T -
    H.initialPhase (n + 1)

theorem terminalFront_eq_phase
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) (n : ℕ) :
    unitTangentData (H.toReadiness.toRawReadiness.globalScaled R n).source =
      MarkedShift.shiftData (H.terminalPhase R n)
        (H.canonicalNextDisplayed R (n + 1)) := by
  exact source_unitTangentData_eq_shift_nextInitial
    (H.toReadiness.toRawReadiness.globalScaled R n)
    (H.toReadiness.toRawReadiness.globalScaled R (n + 1))
    (H.initialPhase (n + 1)) (H.selectedInitial_eq_phase (n + 1))

/-- Assemble the analytic input with canonical displayed and terminal data.
All scalar and analytic fields are inherited from `Readiness`. -/
noncomputable def inputData
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) : InputData R L where
  pre := H.pre
  analytic := (H.toReadiness.inputData R).analytic
  eps_le := (H.toReadiness.inputData R).eps_le
  periodUpper_le := (H.toReadiness.inputData R).periodUpper_le
  periodUpper_le_P1 := (H.toReadiness.inputData R).periodUpper_le_P1
  rawMetric := H.rawMetric
  edgeBudget_le_error := H.edgeBudget_le_error
  nextDisplayed := H.canonicalNextDisplayed R
  terminalFrontReference := fun n => H.canonicalNextDisplayed R (n + 1)
  terminalFrontPhase := H.terminalPhase R
  terminalFront_eq_phase := H.terminalFront_eq_phase R

/-- The exact reachable-system step package.  In particular,
`terminalReference_eq` is definitional after choosing the displayed data from
the scaled sources. -/
noncomputable def stepData
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) :
    StepData R ⟨S, L⟩ where
  input := H.inputData R
  initialPhase := H.initialPhase
  nextDisplayed_eq_phase := by
    intro n
    simpa [inputData, canonicalNextDisplayed] using
      H.selectedInitial_eq_phase n
  rawDiagonalRangeEdge := H.rawDiagonalRangeEdge
  terminalReference_eq := by
    intro n
    rfl

theorem exists_stepData
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : CoherentReadiness R L) : Nonempty (StepData R ⟨S, L⟩) :=
  ⟨H.stepData R⟩

end CoherentReadiness

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicCoherentReadiness
