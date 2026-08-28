import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.MarkingAwareSourcePhaseRigidTransport

/-!
# Phase-rigid transport of exact analytic slice facts

Spatial phase translation and rigid motion preserve every scalar analytic
sidecar used by the successor estimates.  The only non-definitional pieces
are the translated marking increment and the two bounded-range witnesses.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion

open FiniteSmoothRearFamilyMarkingAwareSource

namespace AnalyticSuccessorSliceFacts

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Exact slice facts are invariant under a spatial phase translation followed
by an orientation-preserving rigid motion. -/
def phaseRigid
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (H : AnalyticSuccessorSliceFacts A)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    AnalyticSuccessorSliceFacts (A.phaseRigid phase a w hw) where
  periodUpper := H.periodUpper
  periodLower_pos := H.periodLower_pos
  period_lower := H.period_lower
  period_upper := H.period_upper
  etaFs := H.etaFs
  etaF_deriv := H.etaF_deriv
  etaFs_continuous := H.etaFs_continuous
  etaF_periodic := H.etaF_periodic
  rearNormal_c2 := by
    simpa only [MarkingAwareSource.phaseRigid_Ydot,
      MarkingAwareSource.phaseRigid_Theta, MarkingAwareSource.phaseRigid_delta,
      MarkingAwareSource.phaseRigid_sf] using H.rearNormal_c2
  normal_stopped := by
    intro t ht
    apply H.normal_stopped t
    simpa [
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
      MarkedShift.shiftPathOf] using ht
  markingLower := H.markingLower
  markingUpper := H.markingUpper
  marking_increment := by
    intro t
    rw [MarkingAwareSource.phaseRigid_phi, MarkingAwareSource.phaseRigid_phi,
      MarkingAwareSource.phaseRigid_P]
    rw [show 1 + phase = phase + 1 by ring,
      show 0 + phase = phase by ring, A.phi_shift]
    ring
  markingLower_pos := H.markingLower_pos
  marking_lower := by
    intro t ht u
    rw [MarkingAwareSource.phaseRigid_phi1]
    exact H.marking_lower t (by
      simpa [
        NormalPathC2IncrementVariableSpeed.rigidPath,
        MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
        MarkedShift.shiftPathOf] using ht) (u + phase)
  markingUpper_nonnegative := H.markingUpper_nonnegative
  marking_upper := by
    intro t ht u
    rw [MarkingAwareSource.phaseRigid_phi1]
    exact H.marking_upper t (by
      simpa [
        NormalPathC2IncrementVariableSpeed.rigidPath,
        MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
        MarkedShift.shiftPathOf] using ht) (u + phase)
  marked_bdd0 := by
    intro t
    rcases H.marked_bdd0 t with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rintro y ⟨u, rfl⟩
    apply hc
    exact ⟨u + phase, by
      simp [
        NormalPathC2IncrementVariableSpeed.rigidPath,
        MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
        MarkedShift.shiftPathOf]⟩
  marked_bdd1 := by
    intro t
    rcases H.marked_bdd1 t with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rintro y ⟨u, rfl⟩
    apply hc
    refine ⟨u + phase, ?_⟩
    simp only [
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
      MarkedShift.shiftPathOf]
    rw [iteratedDeriv_comp_add_const]

@[simp] theorem phaseRigid_periodUpper
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (H : AnalyticSuccessorSliceFacts A)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    (H.phaseRigid A phase a w hw).periodUpper = H.periodUpper := rfl

end AnalyticSuccessorSliceFacts

end FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
