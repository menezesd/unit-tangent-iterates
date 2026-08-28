import UnitTangentIterates.VariableSpeedNormalPathPhaseTransport
import UnitTangentIterates.VariableSpeedNormalPathRigidTransport
import UnitTangentIterates.NormalizedC2MarkingPhaseTransport
import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor
import UnitTangentIterates.ConfiguredApproximateDefectPathActualTerminal

noncomputable section
open Function MarkedSpace PathMetric

namespace RichStageDataPhaseRigidTransport

open GaugeRearFamilyVariableTerminal
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalPathC2IncrementVariableSpeed
  NormalizedTerminalMarkingComposition

def move (a w : ℂ) (q : ℝ) (p : Data) : Data :=
  MarkedRigid.rigidData a w (MarkedShift.shiftData q p)

/-- Transport a rich stage by a constant endpoint phase and a common rigid
motion.  The terminal base uses the gauge-correct phase `psi q`, so the
transported terminal marking remains normalized. -/
def transport
    {p front rear : Data} {bound P0 P1 khat G1 Cg c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt)
    (q qfront : ℝ) (a w af wf : ℂ) (hw : ‖w‖ = 1) (hwf : ‖wf‖ = 1)
    (hRange : VariableMarkedTube.GeometricUnitTangentRangeEdge
      (move af wf qfront front) (move a w q rear))
    (hHarnack : VariableMarkedTube.ArclengthHarnackCertificate
      (move a w q rear)) :
    RichStageData (move a w q p) (move af wf qfront front) (move a w q rear)
      bound P0 P1 khat G1 Cg c C dlt := by
  let Gq := MarkedShift.shiftPath q S.stage.increment
  let G := NormalPathC2IncrementVariableSpeed.rigidPath a w hw Gq
  have hcurve : ∀ u, HasDerivAt (⇑(move a w q rear).1)
      ((move a w q rear).2.1 u) u := by
    intro u
    have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
      simpa using (hasDerivAt_id u).add_const q
    have h := (((S.stage.rear_curve_deriv (u + q)).scomp u hi).const_mul w).const_add a
    change HasDerivAt (fun x => a + w * rear.1 (x + q))
      (w * rear.2.1 (u + q)) u
    simpa [Function.comp_def, add_comm] using h
  have hvel : ∀ u, HasDerivAt (⇑(move a w q rear).2.1)
      ((move a w q rear).2.2 u) u := by
    intro u
    have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
      simpa using (hasDerivAt_id u).add_const q
    have h := ((S.stage.rear_vel_deriv (u + q)).scomp u hi).const_mul w
    change HasDerivAt (fun x => w * rear.2.1 (x + q))
      (w * rear.2.2 (u + q)) u
    simpa [Function.comp_def] using h
  refine
    { stage :=
        { increment := G
          increment_geometry := isVariableSpeedNormalPath_rigid a w hw Gq
            (isVariableSpeedNormalPath_shift S.stage.increment
              S.stage.increment_geometry)
          increment_cost := by simpa [G, Gq] using S.stage.increment_cost
          rear_curve_deriv := hcurve
          rear_vel_deriv := hvel
          rear_periodic := by
            intro u
            change a + w * rear.1 (u + 1 + q) = a + w * rear.1 (u + q)
            rw [show u + 1 + q = (u + q) + 1 by ring,
              S.stage.rear_periodic (u + q)]
          rear_curvature_nonnegative := by
            intro u
            change 0 ≤ ((starRingEnd ℂ) (w * rear.2.1 (u + q)) *
              (w * rear.2.2 (u + q))).im
            rw [curvatureNumerator_rigid w _ _ hw]
            exact S.stage.rear_curvature_nonnegative (u + q)
          range_edge := hRange
          rear_harnack := hHarnack }
      terminalBase := move a w (S.marking.marking.psi q) S.terminalBase
      lambda := S.lambda
      Lambda := S.Lambda
      marking := (S.marking.rephase q).rigid a w hw }

/-- Direct phase/rigid packaging of an actual configured gauge terminal.  The
successor front is independent of the path's common rigid motion and is used
only through the supplied physical range certificate. -/
def transportOutput
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data} {n : ℕ}
    {A : ConfiguredApproximateDefectPathActualTerminal.RearCarrier D n}
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
    {bound c C dlt : ℝ}
    (hbound : PathMetric.NormalPath.cost W.increment ≤ bound)
    (q : ℝ) (frontOut : Data) (a w : ℂ) (hw : ‖w‖ = 1)
    (hRange : VariableMarkedTube.GeometricUnitTangentRangeEdge
      frontOut (move a w q W.rear))
    (hHarnack : VariableMarkedTube.ArclengthHarnackCertificate
      (move a w q W.rear)) :
    RichStageData (move a w q (Q n)) frontOut (move a w q W.rear)
      bound
      (ConfiguredApproximateDefectPathRowwise.rowP0 D n)
      (ConfiguredApproximateDefectPathRowwise.rowP1 D n) D.kstar
      (ConfiguredApproximateDefectPathRowwise.rowG1 D n)
      (ConfiguredApproximateDefectPathRowwise.rowCg D n) c C dlt := by
  let Gq := MarkedShift.shiftPath q W.increment
  let G := NormalPathC2IncrementVariableSpeed.rigidPath a w hw Gq
  refine
    { stage :=
        { increment := G
          increment_geometry := isVariableSpeedNormalPath_rigid a w hw Gq
            (isVariableSpeedNormalPath_shift W.increment W.increment_geometry)
          increment_cost := by simpa [G, Gq] using hbound
          rear_curve_deriv := by
            intro u
            have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
              simpa using (hasDerivAt_id u).add_const q
            have h := (((W.rear_curve_deriv (u + q)).scomp u hi).const_mul w).const_add a
            change HasDerivAt (fun x => a + w * W.rear.1 (x + q))
              (w * W.rear.2.1 (u + q)) u
            simpa [Function.comp_def, add_comm] using h
          rear_vel_deriv := by
            intro u
            have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
              simpa using (hasDerivAt_id u).add_const q
            have h := ((W.rear_vel_deriv (u + q)).scomp u hi).const_mul w
            change HasDerivAt (fun x => w * W.rear.2.1 (x + q))
              (w * W.rear.2.2 (u + q)) u
            simpa [Function.comp_def] using h
          rear_periodic := by
            intro u
            change a + w * W.rear.1 (u + 1 + q) = a + w * W.rear.1 (u + q)
            rw [show u + 1 + q = (u + q) + 1 by ring,
              W.rear_periodic (u + q)]
          rear_curvature_nonnegative := by
            intro u
            change 0 ≤ ((starRingEnd ℂ) (w * W.rear.2.1 (u + q)) *
              (w * W.rear.2.2 (u + q))).im
            rw [curvatureNumerator_rigid w _ _ hw]
            exact W.rear_curvature_nonnegative (u + q)
          range_edge := hRange
          rear_harnack := hHarnack }
      terminalBase := move a w (W.marking.marking.psi q) W.terminalBase
      lambda := W.lambda
      Lambda := W.Lambda
      marking := (W.marking.rephase q).rigid a w hw }

/-- The configured phase/rigid transport preserves the unit path time. -/
theorem transportOutput_time_one
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data} {n : ℕ}
    {A : ConfiguredApproximateDefectPathActualTerminal.RearCarrier D n}
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
    {bound c C dlt : ℝ} (hbound : PathMetric.NormalPath.cost W.increment ≤ bound)
    (q : ℝ) (frontOut : Data) (a w : ℂ) (hw : ‖w‖ = 1)
    (hRange : VariableMarkedTube.GeometricUnitTangentRangeEdge
      frontOut (move a w q W.rear))
    (hHarnack : VariableMarkedTube.ArclengthHarnackCertificate
      (move a w q W.rear)) :
    ((transportOutput (c := c) (C := C) (dlt := dlt) W hbound q frontOut
      a w hw hRange hHarnack).stage.increment).T = 1 := by
  simpa [transportOutput, NormalPathC2IncrementVariableSpeed.rigidPath,
    MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
    MarkedShift.shiftPathOf] using W.increment_time_one

/-- Functional integrability is unchanged by a common marking phase and by a
unit rigid motion. -/
theorem transportOutput_functional
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data} {n : ℕ}
    {A : ConfiguredApproximateDefectPathActualTerminal.RearCarrier D n}
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
    {bound c C dlt : ℝ} (hbound : PathMetric.NormalPath.cost W.increment ≤ bound)
    (q : ℝ) (frontOut : Data) (a w : ℂ) (hw : ‖w‖ = 1)
    (hRange : VariableMarkedTube.GeometricUnitTangentRangeEdge
      frontOut (move a w q W.rear))
    (hHarnack : VariableMarkedTube.ArclengthHarnackCertificate
      (move a w q W.rear)) :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      (transportOutput (c := c) (C := C) (dlt := dlt) W hbound q frontOut
        a w hw hRange hHarnack).stage.increment.eta := by
  have F := PeriodicSupNormFunctionalIntegrable.functionalIntegrable_comp_of_jointC2
    W.increment_c2 W.increment_eta_cont W.increment_eta1_cont W.increment_eta2_cont
    (phi := fun u : ℝ => u + q) (phi1 := fun _ => (1 : ℝ))
    (phi2 := fun _ => (0 : ℝ))
    (fun u => by simpa using (hasDerivAt_id u).add_const q)
    (fun u => hasDerivAt_const u 1) continuous_const continuous_const
    (fun u => by ring) (fun _ => rfl) (fun _ => rfl)
  simpa [transportOutput, NormalPathC2IncrementVariableSpeed.rigidPath,
    MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
    MarkedShift.shiftPathOf] using F

end RichStageDataPhaseRigidTransport
