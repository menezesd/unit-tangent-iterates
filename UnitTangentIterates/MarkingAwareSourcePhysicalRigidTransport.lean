import UnitTangentIterates.MarkingAwareSourcePhaseRigidTransport

/-! # Physical rigid transport of a marking-aware source -/

noncomputable section

open Function MarkedSpace PathMetric RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareSource

private theorem rigid_exp_angle (w : ℂ) (hw : ‖w‖ = 1) (theta : ℝ) :
    Complex.exp (Complex.I * ((theta + Complex.arg w : ℝ) : ℂ)) =
      w * Complex.exp (Complex.I * (theta : ℂ)) := by
  have harg : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [mul_comm] using h
  push_cast
  rw [mul_add, Complex.exp_add, harg]
  ring

private theorem rigid_mul_conj (w : ℂ) (hw : ‖w‖ = 1) :
    w * starRingEnd ℂ w = 1 := by
  have harg : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [mul_comm] using h
  rw [← harg]
  exact RearSmoothDependence.exp_mul_conj _

private theorem rigid_frameTangential (w z : ℂ) (hw : ‖w‖ = 1)
    (theta : ℝ) :
    ((w * z) * starRingEnd ℂ
      (Complex.exp (Complex.I * ((theta + Complex.arg w : ℝ) : ℂ)))).re =
      (z * starRingEnd ℂ
        (Complex.exp (Complex.I * (theta : ℂ)))).re := by
  rw [rigid_exp_angle w hw theta, map_mul]
  congr 1
  calc
    w * z * ((starRingEnd ℂ) w *
        (starRingEnd ℂ) (Complex.exp (Complex.I * (theta : ℂ)))) =
      (w * starRingEnd ℂ w) *
        (z * starRingEnd ℂ (Complex.exp (Complex.I * (theta : ℂ)))) := by ring
    _ = _ := by rw [rigid_mul_conj w hw, one_mul]

private theorem rigid_frameNormal (w z : ℂ) (hw : ‖w‖ = 1)
    (theta : ℝ) :
    ((w * z) * starRingEnd ℂ
      (Complex.exp (Complex.I * ((theta + Complex.arg w : ℝ) : ℂ)))).im =
      (z * starRingEnd ℂ
        (Complex.exp (Complex.I * (theta : ℂ)))).im := by
  rw [rigid_exp_angle w hw theta, map_mul]
  congr 1
  calc
    w * z * ((starRingEnd ℂ) w *
        (starRingEnd ℂ) (Complex.exp (Complex.I * (theta : ℂ)))) =
      (w * starRingEnd ℂ w) *
        (z * starRingEnd ℂ (Complex.exp (Complex.I * (theta : ℂ)))) := by ring
    _ = _ := by rw [rigid_mul_conj w hw, one_mul]

namespace MarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}

/-- Apply a Euclidean rigid motion to the physical front and its time velocity
while retaining an already-normalized normal-path presentation.  All scalar
frame components and scalar source bounds are invariant. -/
def physicalRigidFields (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    MarkingAwareSource Gamma P0 kh khat Qmax := by
  let F' : ℝ → ℝ → ℂ := fun t s ↦ a + w * A.F t s
  let Theta' : ℝ → ℝ → ℝ := fun t s ↦ A.Theta t s + Complex.arg w
  let Ydot' : ℝ → ℝ → ℂ := fun t x ↦ w * A.Ydot t x
  have hpsi (t x : ℝ) : rearOwnAngle Theta' A.delta A.sf t x =
      rearOwnAngle A.Theta A.delta A.sf t x + Complex.arg w := by
    simp [rearOwnAngle, RearTrack.rearAngle, Theta']
    ring
  have htan (t x : ℝ) : frameTangential Ydot'
      (rearOwnAngle Theta' A.delta A.sf) t x =
      frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x := by
    unfold frameTangential
    rw [hpsi]
    exact rigid_frameTangential w (A.Ydot t x) hw _
  have hnormal (t x : ℝ) : frameNormal Ydot'
      (rearOwnAngle Theta' A.delta A.sf) t x =
      frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x := by
    unfold frameNormal
    rw [hpsi]
    exact rigid_frameNormal w (A.Ydot t x) hw _
  have hrear (t x : ℝ) : rearOwn F' Theta' A.delta A.sf t x =
      a + w * rearOwn A.F A.Theta A.delta A.sf t x := by
    change a + w * A.F t (A.sf t x) -
        Complex.exp (Complex.I *
          (rearOwnAngle Theta' A.delta A.sf t x : ℂ)) =
      a + w * (A.F t (A.sf t x) -
        Complex.exp (Complex.I *
          (rearOwnAngle A.Theta A.delta A.sf t x : ℂ)))
    rw [hpsi, rigid_exp_angle w hw]
    ring
  refine
    { A with
      F := F'
      Theta := Theta'
      Ydot := Ydot'
      front_frenet := ?_
      angle_frenet := ?_
      rear_time_deriv := ?_
      front_contDiff := ?_
      angle_contDiff := ?_
      frame_regularity := ?_
      front_periodic := ?_
      angle_periodic := ?_
      tangential_zero := ?_
      jacobi := ?_
      eta_link := ?_
      rear_angle_time_deriv := ?_
      rear_angle_time_spatial := A.rear_angle_time_spatial
      mixed_derivative := ?_ }
  · intro t s
    apply ((A.front_frenet t s).const_mul w).const_add a |>.congr_deriv
    exact (rigid_exp_angle w hw (A.Theta t s)).symm
  · intro t s
    simpa [Theta'] using (A.angle_frenet t s).const_add (Complex.arg w)
  · intro t x
    rw [funext (hrear (x := x))]
    simpa [Ydot'] using ((A.rear_time_deriv t x).const_mul w).const_add a
  · exact contDiff_const.add (contDiff_const.mul A.front_contDiff)
  · exact A.angle_contDiff.add contDiff_const
  · cases A.frame_regularity with
    | joint hY hangle =>
        exact .joint (contDiff_const.mul hY)
          (by
            rw [show uncurry (rearOwnAngle Theta' A.delta A.sf) =
              fun z ↦ rearOwnAngle A.Theta A.delta A.sf z.1 z.2 +
                Complex.arg w from funext fun z ↦ hpsi z.1 z.2]
            exact hangle.add contDiff_const)
    | spatial R =>
        let RT : RearOwnFrameDrift.SpatialC2
            (frameTangential Ydot' (rearOwnAngle Theta' A.delta A.sf)) :=
          { xi1 := R.tangential.xi1
            xi2 := R.tangential.xi2
            deriv1 := by
              intro t x
              rw [show frameTangential Ydot'
                (rearOwnAngle Theta' A.delta A.sf) t =
                  frameTangential A.Ydot
                    (rearOwnAngle A.Theta A.delta A.sf) t from funext (htan t)]
              exact R.tangential.deriv1 t x
            deriv2 := R.tangential.deriv2
            continuous0 := by
              rw [show frameTangential Ydot' (rearOwnAngle Theta' A.delta A.sf) =
                frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) from
                  funext fun t ↦ funext (htan t)]
              exact R.tangential.continuous0
            continuous1 := R.tangential.continuous1
            continuous2 := R.tangential.continuous2 }
        let RN : RearOwnFrameDrift.SpatialC2
            (frameNormal Ydot' (rearOwnAngle Theta' A.delta A.sf)) :=
          { xi1 := R.normal.xi1
            xi2 := R.normal.xi2
            deriv1 := by
              intro t x
              rw [show frameNormal Ydot'
                (rearOwnAngle Theta' A.delta A.sf) t =
                  frameNormal A.Ydot
                    (rearOwnAngle A.Theta A.delta A.sf) t from funext (hnormal t)]
              exact R.normal.deriv1 t x
            deriv2 := R.normal.deriv2
            continuous0 := by
              rw [show frameNormal Ydot' (rearOwnAngle Theta' A.delta A.sf) =
                frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) from
                  funext fun t ↦ funext (hnormal t)]
              exact R.normal.continuous0
            continuous1 := R.normal.continuous1
            continuous2 := R.normal.continuous2 }
        exact .spatial {
          tangential := RT
          normal := RN
          tangential1_bound := R.tangential1_bound
          tangential2_bound := R.tangential2_bound
          tangential_period_bound := by
            intro t x hx
            simpa [htan t x] using R.tangential_period_bound t x hx }
  · intro t s
    simp [F', A.front_periodic]
  · intro t s
    simp [Theta', A.angle_periodic]
    ring
  · intro t
    simpa [htan] using A.tangential_zero t
  · intro t x
    have h := A.jacobi t x
    rw [show (fun y ↦ frameNormal Ydot'
      (rearOwnAngle Theta' A.delta A.sf) t y) =
        (fun y ↦ frameNormal A.Ydot
          (rearOwnAngle A.Theta A.delta A.sf) t y) from
      funext (hnormal t)]
    simpa [hnormal] using h
  · intro t u
    exact A.eta_link t u
  · intro t x
    rw [show (fun r ↦ rearOwnAngle Theta' A.delta A.sf r x) =
      (fun r ↦ rearOwnAngle A.Theta A.delta A.sf r x + Complex.arg w) from
        funext fun r ↦ hpsi r x]
    exact (A.rear_angle_time_deriv t x).add_const (Complex.arg w)
  · intro t x
    obtain ⟨Z, hZt, hZx⟩ := A.mixed_derivative t x
    refine ⟨w * Z, ?_, ?_⟩
    · rw [show (fun r ↦ Complex.exp (Complex.I *
          (rearOwnAngle Theta' A.delta A.sf r x : ℂ))) =
        (fun r ↦ w * Complex.exp (Complex.I *
          (rearOwnAngle A.Theta A.delta A.sf r x : ℂ))) by
          funext r
          rw [hpsi, rigid_exp_angle w hw]]
      exact hZt.const_mul w
    · convert hZx.const_mul w using 1
      funext y
      rw [htan, hnormal, hpsi, rigid_exp_angle w hw]
      ring

/-- The physical rear curve is transported by the same Euclidean motion. -/
theorem physicalRigidFields_rearOwn
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) (t x : ℝ) :
    rearOwn (A.physicalRigidFields a w hw).F
        (A.physicalRigidFields a w hw).Theta
        (A.physicalRigidFields a w hw).delta
        (A.physicalRigidFields a w hw).sf t x =
      a + w * rearOwn A.F A.Theta A.delta A.sf t x := by
  simp only [physicalRigidFields]
  simp only [rearOwn, RearTrack.rearTrack, RearTrack.rearAngle]
  rw [show A.Theta t (A.sf t x) + Complex.arg w - A.delta t (A.sf t x) =
    (A.Theta t (A.sf t x) - A.delta t (A.sf t x)) + Complex.arg w by ring]
  rw [rigid_exp_angle w hw]
  ring

/-- Apply the same rigid motion both to the normal-path presentation and to
the physical front fields. -/
def physicalRigid (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    MarkingAwareSource
      (NormalPathC2IncrementVariableSpeed.rigidPath a w hw
        (MarkedShift.shiftPath 0 Gamma))
      P0 kh khat Qmax := by
  let B := (A.phaseRigid 0 a w hw).physicalRigidFields a w hw
  exact B

@[simp] theorem physicalRigidFields_m
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) (t : ℝ) :
    (A.physicalRigidFields a w hw).m t = A.m t := rfl

@[simp] theorem physicalRigidFields_Dd
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) (t : ℝ) :
    (A.physicalRigidFields a w hw).Dd t = A.Dd t := rfl

@[simp] theorem physicalRigidFields_d
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    (A.physicalRigidFields a w hw).d = A.d := rfl

end MarkingAwareSource

end FiniteSmoothRearFamilyMarkingAwareSource
