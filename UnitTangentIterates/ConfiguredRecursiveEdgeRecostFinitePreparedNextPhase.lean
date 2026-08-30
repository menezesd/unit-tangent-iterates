import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.MarkingAwareSourceSelectedInverseCertificate

/-! # Nonmetric provenance for a prepared finite successor -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase

open ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)
  {k : ℕ} {Z : PreparedReachable H k}

/-- Every displayed datum in the prepared successor is the selected rear of
the analytic source from which that successor node was built. -/
theorem nextDisplayed_eq_selected
    (I : PreparedStepData H Z) (n : ℕ) :
    ((I.next H).nodes n).stage.displayed =
      ((I.next H).nodes n).stage.source.selectedRearData 0 := by
  change I.input.nextDisplayed n =
    (I.input.analytic n).source.selectedRearData 0
  exact I.nextDisplayed_eq_selected n

/-- The successor retains the terminal-front phase chosen by its prepared
step. -/
def nextTerminalFrontPhase (I : PreparedStepData H Z) : ℕ → ℝ :=
  I.input.terminalFrontPhase

/-- The terminal front of a successor presentation is the retained phase
shift of the following successor-row displayed datum. -/
theorem nextTerminalFront_eq_phase
    (I : PreparedStepData H Z) (n : ℕ) :
    ((I.next H).presented n).terminal.frontData =
      MarkedShift.shiftData (nextTerminalFrontPhase H I n)
        ((I.next H).nodes (n + 1)).stage.displayed := by
  change (I.boundaryFacts H n).geometry.frontData =
    MarkedShift.shiftData (I.input.terminalFrontPhase n)
      (I.input.nextDisplayed (n + 1))
  calc
    (I.boundaryFacts H n).geometry.frontData =
        unitTangentData (I.input.analytic n).source :=
      (I.boundaryFacts H n).geometry.frontData_eq
    _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (I.input.terminalFrontReference n) :=
      I.input.terminalFront_eq_phase n
    _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (I.input.nextDisplayed (n + 1)) :=
      congrArg (MarkedShift.shiftData (I.input.terminalFrontPhase n))
        (I.terminalReference_eq n)

/-- The raw diagonal range edge of the prepared successor is intrinsic to
the terminal geometry used to construct its presented input. -/
theorem nextRawDiagonalRangeEdge
    (I : PreparedStepData H Z) (n : ℕ) :
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      ((I.next H).nodes (n + 1)).stage.displayed
      ((I.next H).pre H n).geometric.base := by
  let B := I.boundaryFacts H n
  change VariableMarkedTube.GeometricUnitTangentRangeEdge
    (I.input.nextDisplayed (n + 1)) B.geometry.presented
  unfold VariableMarkedTube.GeometricUnitTangentRangeEdge
  have hphase :
      B.geometry.frontData =
        MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (I.input.nextDisplayed (n + 1)) := by
    calc
      B.geometry.frontData = unitTangentData (I.input.analytic n).source :=
        B.geometry.frontData_eq
      _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
            (I.input.terminalFrontReference n) :=
        I.input.terminalFront_eq_phase n
      _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
            (I.input.nextDisplayed (n + 1)) :=
        congrArg (MarkedShift.shiftData (I.input.terminalFrontPhase n))
          (I.terminalReference_eq n)
  have hnextTube :
      IsTubeMember
        (rearPeriod (I.input.analytic (n + 1)).source 0) 0 0
        (I.input.nextDisplayed (n + 1)) := by
    rw [I.nextDisplayed_eq_selected (n + 1)]
    exact
      FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearData_tube
        (I.input.analytic (n + 1)).source 0
  have hc :
      0 < rearPeriod (I.input.analytic (n + 1)).source 0 :=
    (I.input.analytic (n + 1)).source.rear_period_pos 0
  have hfront :
      range (ev B.geometry.frontData) =
        range (ev (I.input.nextDisplayed (n + 1))) := by
    have hshiftTube := MarkedShift.isTubeMember_shiftData hnextTube
      (I.input.terminalFrontPhase n)
    calc
      range (ev B.geometry.frontData) =
          range (ev (MarkedShift.shiftData
            (I.input.terminalFrontPhase n)
            (I.input.nextDisplayed (n + 1)))) :=
        congrArg (fun p : Data ↦ range (ev p)) hphase
      _ = range (ev (I.input.nextDisplayed (n + 1))) := by
        exact (range_ev hc hshiftTube).trans
          ((FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.range_shiftData
            (I.input.nextDisplayed (n + 1))
            (I.input.terminalFrontPhase n)).trans
              (range_ev hc hnextTube).symm)
  calc
    range (⇑(I.input.nextDisplayed (n + 1)).1) =
        range (ev (I.input.nextDisplayed (n + 1))) :=
      (range_ev hc hnextTube).symm
    _ =
        range (ev B.geometry.frontData) := hfront.symm
    _ = range ((I.input.analytic n).source.F
          (I.input.pre (n + 1)).path.T) := B.geometry.front_range
    _ = range (VariableMarkedTube.geometricUnitTangent
          B.geometry.presented) := by
      have hgeometric :
          VariableMarkedTube.geometricUnitTangent B.geometry.presented =
            normalizedUnitTangent B.geometry.presented := by
        funext u
        rw [VariableMarkedTube.geometricUnitTangent, normalizedUnitTangent,
          norm_vel_eq_perim B.geometry.zero_floor_tube u]
      calc
        range ((I.input.analytic n).source.F
            (I.input.pre (n + 1)).path.T) =
            range (UnitTangent.unitTangentMap (ev B.geometry.presented)) :=
          B.geometry.tangent_range.symm
        _ = range (normalizedUnitTangent B.geometry.presented) :=
          range_unitTangentMap_ev_eq_normalized
            B.geometry.physical.cq_pos B.geometry.zero_floor_tube
        _ = range (VariableMarkedTube.geometricUnitTangent
            B.geometry.presented) := congrArg range hgeometric.symm

/-- The front datum retained by each successor presentation is exactly the
canonical unit-tangent datum of that successor node's source. -/
theorem nextFrontData_eq_source
    (I : PreparedStepData H Z) (n : ℕ) :
    ((I.next H).presented n).terminal.frontData =
      unitTangentData ((I.next H).nodes n).stage.source := by
  change (I.boundaryFacts H n).geometry.frontData =
    unitTangentData (I.input.analytic n).source
  exact (I.boundaryFacts H n).geometry.frontData_eq

end ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase
