import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.VariableSpeedNormalPathPhaseTransport
import UnitTangentIterates.VariableSpeedNormalPathRigidTransport

/-!
# Phase and rigid transport of marking-aware analytic sources

The physical arclength front data are unchanged by reanchoring the normalized
parameter of a normal path and by a common rigid motion.  Only the marking
which links normalized parameter to physical arclength must be precomposed by
the phase translation.
-/

noncomputable section

open Function MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareSource

open NormalPathC2IncrementVariableSpeed

/-- Transport a marking-aware source through a constant phase shift of its
normal path followed by a unit rigid motion. -/
def MarkingAwareSource.phaseRigid
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    MarkingAwareSource
      (rigidPath a w hw (MarkedShift.shiftPath phase Gamma))
      P0 kh khat Qmax := by
  let tau : ℝ → ℝ := fun u ↦ u + phase
  exact
    { A with
      phi := fun t u ↦ A.phi t (tau u)
      phi1 := fun t u ↦ A.phi1 t (tau u)
      phi2 := fun t u ↦ A.phi2 t (tau u)
      frame_regularity := by
        cases A.frame_regularity with
        | joint velocity angle => exact .joint velocity angle
        | spatial R =>
            exact .spatial
              { R with
                tangential_period_bound := by
                  intro t x hx
                  simpa [rigidPath, MarkedRigid.NormalPathRigid.rigidPathOf,
                    MarkedShift.shiftPath, MarkedShift.shiftPathOf] using
                    R.tangential_period_bound t x hx }
      eta_link := by
        intro t u
        simpa [rigidPath, MarkedRigid.NormalPathRigid.rigidPathOf,
          MarkedShift.shiftPath, MarkedShift.shiftPathOf, tau] using
          A.eta_link t (u + phase)
      phi_shift := by
        intro t u
        simpa [tau, add_assoc, add_left_comm, add_comm] using
          A.phi_shift t (u + phase)
      phi_deriv := by
        intro t u
        convert (A.phi_deriv t (tau u)).scomp u
          (by simpa [tau] using (hasDerivAt_id u).add_const phase) using 1 <;>
          simp [tau, Function.comp_def]
      phi1_deriv := by
        intro t u
        convert (A.phi1_deriv t (tau u)).scomp u
          (by simpa [tau] using (hasDerivAt_id u).add_const phase) using 1 <;>
          simp [tau, Function.comp_def]
      phi1_continuous := by
        intro t
        exact (A.phi1_continuous t).comp (continuous_id.add continuous_const)
      phi2_continuous := by
        intro t
        exact (A.phi2_continuous t).comp (continuous_id.add continuous_const) }

namespace MarkingAwareSource

@[simp] theorem phaseRigid_P
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).P = A.P := by simp [phaseRigid]

@[simp] theorem phaseRigid_etaF
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).etaF = A.etaF := by simp [phaseRigid]

@[simp] theorem phaseRigid_Ydot
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).Ydot = A.Ydot := by simp [phaseRigid]

@[simp] theorem phaseRigid_Theta
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).Theta = A.Theta := by simp [phaseRigid]

@[simp] theorem phaseRigid_delta
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).delta = A.delta := by simp [phaseRigid]

@[simp] theorem phaseRigid_sf
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).sf = A.sf := by simp [phaseRigid]

@[simp] theorem phaseRigid_m
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).m = A.m := by simp [phaseRigid]

@[simp] theorem phaseRigid_Dd
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).Dd = A.Dd := by simp [phaseRigid]

@[simp] theorem phaseRigid_d
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.phaseRigid phase a w hw).d = A.d := by simp [phaseRigid]

@[simp] theorem phaseRigid_phi
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) (t u : ℝ) :
    (A.phaseRigid phase a w hw).phi t u = A.phi t (u + phase) := by
  simp [phaseRigid]

@[simp] theorem phaseRigid_phi1
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) (t u : ℝ) :
    (A.phaseRigid phase a w hw).phi1 t u = A.phi1 t (u + phase) := by
  simp [phaseRigid]

end MarkingAwareSource

end FiniteSmoothRearFamilyMarkingAwareSource
