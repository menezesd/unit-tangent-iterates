import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveSidecarsPhaseRigid
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSliceFactsPhaseRigid
import UnitTangentIterates.MarkingAwareSourcePhysicalRigidTransport

/-!
# Rigid transport of recursive exact analytic successors

The marking-only `phaseRigid` transport and the physical-field-only
`physicalRigidFields` transport each preserve all analytic certificates.  An
endpoint-range witness is required when either half is used in isolation,
because only their composition moves the path endpoint and the physical front
together.  The combined transport, and hence `physicalRigid`, preserve the
complete recursive package without an additional hypothesis.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

private theorem rigid_frameNormal (w z : ℂ) (hw : ‖w‖ = 1)
    (theta : ℝ) :
    ((w * z) * starRingEnd ℂ
      (Complex.exp (Complex.I * ((theta + Complex.arg w : ℝ) : ℂ)))).im =
      (z * starRingEnd ℂ
        (Complex.exp (Complex.I * (theta : ℂ)))).im := by
  have harg : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [mul_comm] using h
  have hunit : w * starRingEnd ℂ w = 1 := by
    rw [← harg]
    exact RearSmoothDependence.exp_mul_conj _
  rw [show Complex.exp (Complex.I * ((theta + Complex.arg w : ℝ) : ℂ)) =
      w * Complex.exp (Complex.I * (theta : ℂ)) by
    push_cast
    rw [mul_add, Complex.exp_add, harg]
    ring, map_mul]
  congr 1
  calc
    w * z * (starRingEnd ℂ w *
        starRingEnd ℂ (Complex.exp (Complex.I * (theta : ℂ)))) =
      (w * starRingEnd ℂ w) *
        (z * starRingEnd ℂ (Complex.exp (Complex.I * (theta : ℂ)))) := by
          ring
    _ = _ := by rw [hunit, one_mul]

namespace MarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- The scalar rear-frame normal is unchanged when the physical fields are
moved by an orientation-preserving Euclidean rigid motion. -/
theorem physicalRigidFields_frameNormal
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    frameNormal (A.physicalRigidFields a w hw).Ydot
      (rearOwnAngle (A.physicalRigidFields a w hw).Theta
        (A.physicalRigidFields a w hw).delta
        (A.physicalRigidFields a w hw).sf) =
    frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) := by
  funext t x
  unfold frameNormal rearOwnAngle RearTrack.rearAngle
  simp only [
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields]
  rw [show A.Theta t (A.sf t x) + Complex.arg w - A.delta t (A.sf t x) =
    (A.Theta t (A.sf t x) - A.delta t (A.sf t x)) + Complex.arg w by ring]
  exact rigid_frameNormal w (A.Ydot t x) hw _

/-- The scalar tangential component is likewise unchanged by the common
orientation-preserving rigid motion. -/
theorem physicalRigidFields_frameTangential
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    frameTangential (A.physicalRigidFields a w hw).Ydot
      (rearOwnAngle (A.physicalRigidFields a w hw).Theta
        (A.physicalRigidFields a w hw).delta
        (A.physicalRigidFields a w hw).sf) =
    frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) := by
  funext t x
  unfold frameTangential rearOwnAngle RearTrack.rearAngle
  simp only [
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields]
  rw [show A.Theta t (A.sf t x) + Complex.arg w - A.delta t (A.sf t x) =
    (A.Theta t (A.sf t x) - A.delta t (A.sf t x)) + Complex.arg w by ring]
  have harg : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [mul_comm] using h
  have hunit : w * starRingEnd ℂ w = 1 := by
    rw [← harg]
    exact RearSmoothDependence.exp_mul_conj _
  rw [show Complex.exp
      (Complex.I * (((A.Theta t (A.sf t x) - A.delta t (A.sf t x)) +
        Complex.arg w : ℝ) : ℂ)) =
      w * Complex.exp (Complex.I *
        ((A.Theta t (A.sf t x) - A.delta t (A.sf t x) : ℝ) : ℂ)) by
    push_cast
    rw [mul_add, Complex.exp_add, harg]
    ring, map_mul]
  congr 1
  calc
    w * A.Ydot t x * (starRingEnd ℂ w *
        starRingEnd ℂ (Complex.exp (Complex.I *
          ((A.Theta t (A.sf t x) - A.delta t (A.sf t x) : ℝ) : ℂ)))) =
      (w * starRingEnd ℂ w) *
        (A.Ydot t x * starRingEnd ℂ (Complex.exp (Complex.I *
          ((A.Theta t (A.sf t x) - A.delta t (A.sf t x) : ℝ) : ℂ)))) := by
            ring
    _ = _ := by rw [hunit, one_mul]

end MarkingAwareSource

namespace SpatialFrameRegularity

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

def phaseRigid
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    SpatialFrameRegularity
      (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
        (MarkedShift.shiftPath phase Gamma))
      (A.phaseRigid phase a w hw).Ydot
      (A.phaseRigid phase a w hw).Theta
      (A.phaseRigid phase a w hw).delta
      (A.phaseRigid phase a w hw).sf
      (A.phaseRigid phase a w hw).P
      (A.phaseRigid phase a w hw).m kh Qmax := by
  exact
    { R with
      tangential_period_bound := by
        intro t x hx
        simpa [NormalPathC2IncrementVariableSpeed.rigidPath,
          MarkedRigid.NormalPathRigid.rigidPathOf,
          MarkedShift.shiftPath, MarkedShift.shiftPathOf] using
          R.tangential_period_bound t x hx }

def physicalRigidFields
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    SpatialFrameRegularity Gamma
      (A.physicalRigidFields a w hw).Ydot
      (A.physicalRigidFields a w hw).Theta
      (A.physicalRigidFields a w hw).delta
      (A.physicalRigidFields a w hw).sf
      (A.physicalRigidFields a w hw).P
      (A.physicalRigidFields a w hw).m kh Qmax :=
  { tangential := by
      exact
        { xi1 := R.tangential.xi1
          xi2 := R.tangential.xi2
          deriv1 := by
            simpa only [MarkingAwareSource.physicalRigidFields_frameTangential]
              using R.tangential.deriv1
          deriv2 := R.tangential.deriv2
          continuous0 := by
            simpa only [MarkingAwareSource.physicalRigidFields_frameTangential]
              using R.tangential.continuous0
          continuous1 := R.tangential.continuous1
          continuous2 := R.tangential.continuous2 }
    normal := by
      simpa only [MarkingAwareSource.physicalRigidFields_frameNormal]
        using R.normal
    tangential1_bound := by
      exact R.tangential1_bound
    tangential2_bound := by
      exact R.tangential2_bound
    tangential_period_bound := by
      simpa only [MarkingAwareSource.physicalRigidFields_frameTangential]
        using R.tangential_period_bound }

end SpatialFrameRegularity

namespace AnalyticSuccessorSliceFacts

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Exact slice facts are invariant under rigid motion of the physical source
fields while the normalized path presentation is held fixed. -/
def physicalRigidFields
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (H : AnalyticSuccessorSliceFacts A)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    AnalyticSuccessorSliceFacts (A.physicalRigidFields a w hw) where
  periodUpper := H.periodUpper
  periodLower_pos := H.periodLower_pos
  period_lower := H.period_lower
  period_upper := H.period_upper
  etaFs := H.etaFs
  etaF_deriv := H.etaF_deriv
  etaFs_continuous := H.etaFs_continuous
  etaF_periodic := H.etaF_periodic
  rearNormal_c2 := by
    simpa only [MarkingAwareSource.physicalRigidFields_frameNormal]
      using H.rearNormal_c2
  normal_stopped := by
    simpa only [MarkingAwareSource.physicalRigidFields_frameNormal]
      using H.normal_stopped
  markingLower := H.markingLower
  markingUpper := H.markingUpper
  marking_increment := H.marking_increment
  markingLower_pos := H.markingLower_pos
  marking_lower := H.marking_lower
  markingUpper_nonnegative := H.markingUpper_nonnegative
  marking_upper := H.marking_upper
  marked_bdd0 := H.marked_bdd0
  marked_bdd1 := H.marked_bdd1

end AnalyticSuccessorSliceFacts

namespace SelectionBounds

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Fresh successor-selection bounds depend only on the scalar steering and
period fields, all of which are definitionally fixed by `physicalRigidFields`.
-/
def physicalRigidFields
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : SelectionBounds A)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    SelectionBounds (A.physicalRigidFields a w hw) :=
  { periodLower := S.periodLower
    periodUpper := S.periodUpper
    Md := S.Md
    MP := S.MP
    periodLower_pos := S.periodLower_pos
    period_lower := S.period_lower
    period_upper := S.period_upper
    Md_nonnegative := S.Md_nonnegative
    MP_nonnegative := S.MP_nonnegative
    normalizedCurvatureTime_le := S.normalizedCurvatureTime_le
    periodTime_le := S.periodTime_le }

end SelectionBounds

namespace RecursiveExactSidecars

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Transport the recursive exact package through physical rigid motion of
the source fields. -/
def physicalRigidFields
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : RecursiveExactSidecars A)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    RecursiveExactSidecars (A.physicalRigidFields a w hw) :=
  RecursiveExactSidecars.ofSource _
    (SelectionBounds.physicalRigidFields A S.selection a w hw)

end RecursiveExactSidecars

namespace RecursiveAnalyticSuccessor

variable {p q c d : Data} {Gamma : NormalPath p q} {Delta : NormalPath c d}
  {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- Transport through the marking/path half of the rigid normalization.  The
endpoint-range premise records the geometric compatibility which this half,
used alone, does not imply. -/
def phaseRigid
    (R : RecursiveAnalyticSuccessor Delta A
      periodLower kap khatNext QmaxNext)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1)
    (terminalRange :
      Set.range ((R.source.phaseRigid phase a w hw).F
        (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
          (MarkedShift.shiftPath phase Delta)).T) =
      Set.range (MarkedRigid.rigidData a w
        (MarkedShift.shiftData phase d)).1) :
    RecursiveAnalyticSuccessor
      (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
        (MarkedShift.shiftPath phase Delta))
      (A.phaseRigid phase a w hw) periodLower kap khatNext QmaxNext :=
  ⟨R.source.phaseRigid phase a w hw,
    R.slice.phaseRigid R.source phase a w hw,
    FiniteSmoothRearFamilyMarkingAwareRecursiveSidecarsPhaseRigid.RecursiveExactSidecars.phaseRigid
      R.source R.sidecars phase a w hw,
    SpatialFrameRegularity.phaseRigid R.source R.spatial phase a w hw,
    R.terminalCurvature_nonnegative, terminalRange⟩

/-- Transport through the physical-field half of the rigid normalization.
The endpoint-range premise is necessary because the path endpoint is held
fixed by this half. -/
def physicalRigidFields
    (R : RecursiveAnalyticSuccessor Delta A
      periodLower kap khatNext QmaxNext)
    (a w : ℂ) (hw : ‖w‖ = 1)
    (terminalRange :
      Set.range ((R.source.physicalRigidFields a w hw).F Delta.T) =
        Set.range d.1) :
    RecursiveAnalyticSuccessor Delta (A.physicalRigidFields a w hw)
      periodLower kap khatNext QmaxNext :=
  ⟨R.source.physicalRigidFields a w hw,
    AnalyticSuccessorSliceFacts.physicalRigidFields R.source R.slice a w hw,
    RecursiveExactSidecars.physicalRigidFields R.source R.sidecars a w hw,
    SpatialFrameRegularity.physicalRigidFields R.source R.spatial a w hw,
    R.terminalCurvature_nonnegative, terminalRange⟩

/-- Move the path presentation and the physical source fields together.  This
is the unconditional generic transport: all recursive certificates and the
terminal geometry are preserved. -/
def phasePhysicalRigid
    (R : RecursiveAnalyticSuccessor Delta A
      periodLower kap khatNext QmaxNext)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    RecursiveAnalyticSuccessor
      (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
        (MarkedShift.shiftPath phase Delta))
      ((A.phaseRigid phase a w hw).physicalRigidFields a w hw)
      periodLower kap khatNext QmaxNext := by
  let B := R.source.phaseRigid phase a w hw
  refine ⟨B.physicalRigidFields a w hw,
    AnalyticSuccessorSliceFacts.physicalRigidFields B
      (R.slice.phaseRigid R.source phase a w hw) a w hw,
    RecursiveExactSidecars.physicalRigidFields B
      (FiniteSmoothRearFamilyMarkingAwareRecursiveSidecarsPhaseRigid.RecursiveExactSidecars.phaseRigid
        R.source R.sidecars phase a w hw)
      a w hw,
    SpatialFrameRegularity.physicalRigidFields B
      (SpatialFrameRegularity.phaseRigid R.source R.spatial phase a w hw)
      a w hw,
    R.terminalCurvature_nonnegative, ?_⟩
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    rcases Set.ext_iff.1 R.terminalRange (R.source.F Delta.T s) |>.mp
      ⟨s, rfl⟩ with ⟨u, hu⟩
    refine ⟨u - phase, ?_⟩
    simp only [B, MarkingAwareSource.physicalRigidFields,
      MarkingAwareSource.phaseRigid, MarkedRigid.rigidData_curve,
      MarkedShift.shiftData_curve,
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
      MarkedShift.shiftPathOf]
    rw [sub_add_cancel, hu]
  · rintro ⟨u, rfl⟩
    rcases Set.ext_iff.1 R.terminalRange (d.1 (u + phase)) |>.mpr
      ⟨u + phase, rfl⟩ with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simp only [B, MarkingAwareSource.physicalRigidFields,
      MarkingAwareSource.phaseRigid, MarkedRigid.rigidData_curve,
      MarkedShift.shiftData_curve,
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
      MarkedShift.shiftPathOf]
    rw [hs]

/-- The standard physical rigid transport is the zero-phase specialization
of `phasePhysicalRigid`, rebased to the correspondingly transported phantom
predecessor source. -/
def physicalRigid
    (R : RecursiveAnalyticSuccessor Delta A
      periodLower kap khatNext QmaxNext)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    RecursiveAnalyticSuccessor
      (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
        (MarkedShift.shiftPath 0 Delta))
      (A.physicalRigid a w hw) periodLower kap khatNext QmaxNext :=
  (phasePhysicalRigid R 0 a w hw).rebase (A.physicalRigid a w hw)

end RecursiveAnalyticSuccessor

end FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport
