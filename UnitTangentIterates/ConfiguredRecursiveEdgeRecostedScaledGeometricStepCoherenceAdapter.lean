import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep
import UnitTangentIterates.CoherentPhaseReachableMetricRange

/-!
# A global scaled geometric step as coherent phase data

This leaf extracts the four facts required by
`CoherentPhaseReachableMetricRange.StepCoherence` directly from one global
`StepInput`.  It is independent of any recursive provider or tail indexing.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedScaledGeometricStepCoherenceAdapter

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

/-- The displayed data in the current global column. -/
def current (_H : StepInput X) (n : ℕ) : Data :=
  (X.stage n).displayed

/-- The displayed data in the theorem-produced next global column. -/
def next (H : StepInput X) (n : ℕ) : Data :=
  (H.next.stage n).displayed

/-- The unshifted canonical endpoint selected in the current row. -/
def canonical (H : StepInput X) (n : ℕ) : Data :=
  (H.rowBounds.row n).presented

/-- The successor-row datum referenced by the physical terminal front. -/
def terminalReference (H : StepInput X) (n : ℕ) : Data :=
  H.mappedInitial (n + 1)

/-- The selected canonical endpoint is the exact geometric unit-tangent image
of the current datum in the next row. -/
theorem rawDiagonalRangeEdge (H : StepInput X) (n : ℕ) :
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (current H (n + 1)) (canonical H n) := by
  let A := H.rowBounds.row n
  let I := NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl
    A.presented
  have hcanonical : range (X.stage (n + 1)).displayed.1 =
      range (UnitTangent.unitTangentMap (ev A.presented)) :=
    (X.invariant.pathEndRange n).symm.trans A.terminalInput.canonical_range
  exact GaugeRearFamilyVariableTerminal.geometricRangeEdge_of_flowMarking
    A.terminalInput.physical.cq_pos I.lambda_pos
    A.terminalInput.zero_floor_tube I.marking
    (by simpa [I, NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl]
      using continuous_id)
    (by simpa [I, NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl]
      using strictMono_id)
    I.psi_zero hcanonical

/-- A single global theorem-produced step supplies exactly the abstract
coherent phase record. -/
def toStepCoherence (H : StepInput X) :
    StepCoherence (current H) (next H) (canonical H)
      (terminalReference H) where
  initialPhase := H.mappedInitial_phase
  nextDisplayed_eq_phase n := by
    change (H.next.stage n).displayed =
      MarkedShift.shiftData (H.mappedInitial_phase n)
        (H.rowBounds.row n).presented
    exact H.mappedInitial_eq_phase n
  rawDiagonalRangeEdge := rawDiagonalRangeEdge H
  terminalReference_eq n := by
    change H.mappedInitial (n + 1) = (H.next.stage (n + 1)).displayed
    rfl

/-- The actual terminal unit-tangent datum is retained as a cyclic phase of
the exact terminal reference used by `toStepCoherence`. -/
theorem terminalFront_eq_phase (H : StepInput X) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (H.scaled n).source =
      MarkedShift.shiftData (H.mappedTerminalFront_phase n)
        (terminalReference H n) :=
  H.mappedTerminalFront_eq_phase n

end ConfiguredRecursiveEdgeRecostedScaledGeometricStepCoherenceAdapter
