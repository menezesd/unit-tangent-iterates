import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometryCore
import UnitTangentIterates.PinchedSliceData
import UnitTangentIterates.PhysicalRearLimitKinematicClosure

/-! # Canonical marked unit-tangent front of a presented terminal rear -/

noncomputable section

set_option maxHeartbeats 1000000

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  NormalizedSelectedRearClosure NormalizedSteeringPhysicalRescaling

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

def normalizedFront
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (u : ℝ) : ℂ :=
  A.F Gamma.T (A.P Gamma.T * u)

def normalizedFrontVelocity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (u : ℝ) : ℂ :=
  (A.P Gamma.T : ℂ) *
    Complex.exp (Complex.I * (A.Theta Gamma.T (A.P Gamma.T * u) : ℂ))

def normalizedFrontAcceleration
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (u : ℝ) : ℂ :=
  ((A.P Gamma.T : ℂ) ^ 2) *
    (Complex.I * (A.K Gamma.T (A.P Gamma.T * u) : ℂ) *
      Complex.exp (Complex.I * (A.Theta Gamma.T (A.P Gamma.T * u) : ℂ)))

theorem terminalFrontCurvature_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (A.K Gamma.T) := by
  have htheta : ContDiff ℝ 1 (A.Theta Gamma.T) :=
    A.angle_contDiff.comp (contDiff_const.prodMk contDiff_id)
  have heq : deriv (A.Theta Gamma.T) = A.K Gamma.T :=
    funext fun s ↦ (A.angle_frenet Gamma.T s).deriv
  rw [← heq]
  exact htheta.continuous_deriv (by norm_num)

theorem terminalFrontCurvature_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Periodic (A.K Gamma.T) (A.P Gamma.T) :=
  SelectedInverseTube.curvature_periodic
    (A.front_frenet Gamma.T) (A.angle_frenet Gamma.T)
    (A.front_periodic Gamma.T)

theorem normalizedFront_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (u : ℝ) :
    HasDerivAt (normalizedFront A) (normalizedFrontVelocity A u) u := by
  have hi : HasDerivAt (fun z : ℝ ↦ A.P Gamma.T * z) (A.P Gamma.T) u := by
    simpa using (hasDerivAt_id u).const_mul (A.P Gamma.T)
  simpa [normalizedFront, normalizedFrontVelocity, smul_eq_mul, mul_comm] using
    (A.front_frenet Gamma.T (A.P Gamma.T * u)).scomp u hi

theorem normalizedFrontVelocity_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (u : ℝ) :
    HasDerivAt (normalizedFrontVelocity A) (normalizedFrontAcceleration A u) u := by
  have hi : HasDerivAt (fun z : ℝ ↦ A.P Gamma.T * z) (A.P Gamma.T) u := by
    simpa using (hasDerivAt_id u).const_mul (A.P Gamma.T)
  have htheta := (A.angle_frenet Gamma.T (A.P Gamma.T * u)).scomp u hi
  have h := (((htheta.ofReal_comp).const_mul Complex.I).cexp).const_mul
    (A.P Gamma.T : ℂ)
  convert h using 1
  · simp only [normalizedFrontAcceleration, smul_eq_mul, Function.comp_apply]
    push_cast
    ring

theorem normalizedFront_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Periodic (normalizedFront A) 1 := by
  intro u
  simp only [normalizedFront, mul_add, mul_one]
  exact A.front_periodic Gamma.T (A.P Gamma.T * u)

theorem normalizedFrontVelocity_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Periodic (normalizedFrontVelocity A) 1 := by
  intro u
  simp only [normalizedFrontVelocity, mul_add, mul_one]
  rw [A.angle_periodic Gamma.T (A.P Gamma.T * u)]
  have hcast : ((A.Theta Gamma.T (A.P Gamma.T * u) + 2 * Real.pi : ℝ) : ℂ) =
      (A.Theta Gamma.T (A.P Gamma.T * u) : ℂ) + 2 * Real.pi := by
    push_cast
    ring
  rw [hcast, mul_add, Complex.exp_add]
  have h2pi : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = 2 * Real.pi * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]

theorem normalizedFrontAcceleration_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Periodic (normalizedFrontAcceleration A) 1 := by
  intro u
  simp only [normalizedFrontAcceleration, mul_add, mul_one]
  rw [terminalFrontCurvature_periodic A (A.P Gamma.T * u),
    A.angle_periodic Gamma.T (A.P Gamma.T * u)]
  have hcast : ((A.Theta Gamma.T (A.P Gamma.T * u) + 2 * Real.pi : ℝ) : ℂ) =
      (A.Theta Gamma.T (A.P Gamma.T * u) : ℂ) + 2 * Real.pi := by
    push_cast
    ring
  rw [hcast, mul_add, Complex.exp_add]
  have h2pi : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = 2 * Real.pi * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]

/-- Canonical normalized marked data of the unit-tangent front retraced by the
terminal selected rear. -/
def unitTangentData
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Data :=
  let X := normalizedFront A
  let V := normalizedFrontVelocity A
  let B := normalizedFrontAcceleration A
  let hXc : Continuous X := Differentiable.continuous
    (fun u ↦ (normalizedFront_deriv A u).differentiableAt)
  let hVc : Continuous V := Differentiable.continuous
    (fun u ↦ (normalizedFrontVelocity_deriv A u).differentiableAt)
  let hKc := terminalFrontCurvature_continuous A
  let hThetac : Continuous (A.Theta Gamma.T) :=
    A.angle_contDiff.continuous.comp (continuous_const.prodMk continuous_id)
  let hBc : Continuous B := by
    exact continuous_const.mul ((continuous_const.mul
      (Complex.continuous_ofReal.comp
        (hKc.comp (continuous_const.mul continuous_id)))).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp
          (hThetac.comp (continuous_const.mul continuous_id))))))
  (PinchedPath.sliceBCF X hXc (normalizedFront_periodic A),
    PinchedPath.sliceBCF V hVc (normalizedFrontVelocity_periodic A),
    PinchedPath.sliceBCF B hBc (normalizedFrontAcceleration_periodic A))

@[simp] theorem unitTangentData_curve
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ⇑(unitTangentData A).1 = normalizedFront A := by
  simp [unitTangentData]

@[simp] theorem unitTangentData_velocity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ⇑(unitTangentData A).2.1 = normalizedFrontVelocity A := by
  simp [unitTangentData]

theorem unitTangentData_perim
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    perim (unitTangentData A) = A.P Gamma.T := by
  rw [perim, unitTangentData_velocity]
  simp [normalizedFrontVelocity, abs_of_pos (A.period_pos Gamma.T)]

theorem ev_unitTangentData
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ev (unitTangentData A) = A.F Gamma.T := by
  funext s
  rw [ev, unitTangentData_curve, normalizedFront, unitTangentData_perim]
  field_simp [ne_of_gt (A.period_pos Gamma.T)]

def normalizedTerminalSteering
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : SteeringData kh where
  K := fun u ↦ A.P Gamma.T * A.K Gamma.T (A.P Gamma.T * u) +
    (1 - A.P Gamma.T) * Real.sin (A.delta Gamma.T (A.P Gamma.T * u))
  delta := fun u ↦ A.delta Gamma.T (A.P Gamma.T * u)
  K_periodic := by
    intro u
    simp only [mul_add, mul_one]
    rw [terminalFrontCurvature_periodic A, A.steering_periodic Gamma.T]
  delta_periodic := by
    intro u
    simp only [mul_add, mul_one]
    rw [A.steering_periodic Gamma.T]
  delta_mem := fun u ↦
    ⟨A.strip_nonnegative Gamma.T _, A.strip_le Gamma.T _⟩
  steering := by
    intro u
    have hi : HasDerivAt (fun z : ℝ ↦ A.P Gamma.T * z)
        (A.P Gamma.T) u := by
      simpa using (hasDerivAt_id u).const_mul (A.P Gamma.T)
    convert (A.steering Gamma.T (A.P Gamma.T * u)).scomp u hi using 1 <;>
      simp only [smul_eq_mul] <;> ring

theorem deltaPhys_normalizedTerminalSteering
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    deltaPhys (normalizedTerminalSteering A) (perim (unitTangentData A)) =
      A.delta Gamma.T := by
  funext s
  simp only [deltaPhys, normalizedTerminalSteering, unitTangentData_perim]
  congr 1
  field_simp [ne_of_gt (A.period_pos Gamma.T)]

theorem curvaturePhys_normalizedTerminalSteering
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    curvaturePhys (normalizedTerminalSteering A) (perim (unitTangentData A)) =
      A.K Gamma.T := by
  funext s
  simp only [curvaturePhys, normalizedTerminalSteering, unitTangentData_perim,
    deltaPhys]
  field_simp [ne_of_gt (A.period_pos Gamma.T)]
  ring

theorem normalizedTerminalCurvature_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (normalizedTerminalSteering A).K := by
  have hK := terminalFrontCurvature_continuous A
  have hd : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact (continuous_const.mul (hK.comp (continuous_const.mul continuous_id))).add
    (continuous_const.mul
      (Real.continuous_sin.comp (hd.comp (continuous_const.mul continuous_id))))

theorem thetaPhys_normalizedTerminalSteering
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    thetaPhys (normalizedTerminalSteering A) (perim (unitTangentData A))
      (A.Theta Gamma.T 0) = A.Theta Gamma.T := by
  let d := normalizedTerminalSteering A
  let P := perim (unitTangentData A)
  let th0 := A.Theta Gamma.T 0
  have hKc : Continuous d.K := by
    exact normalizedTerminalCurvature_continuous A
  have hcurv : curvaturePhys d P = A.K Gamma.T :=
    curvaturePhys_normalizedTerminalSteering A
  funext s
  have hz : ∀ x, HasDerivAt
      (fun y ↦ thetaPhys d P th0 y - A.Theta Gamma.T y) 0 x := by
    intro x
    simpa [hcurv] using
      (hasDerivAt_thetaPhys (P := P) (theta0 := th0) d hKc x).sub
        (A.angle_frenet Gamma.T x)
  have hc := is_const_of_deriv_eq_zero
    (fun x ↦ (hz x).differentiableAt) (fun x ↦ (hz x).deriv) s 0
  have hzero : thetaPhys d P th0 0 - A.Theta Gamma.T 0 = 0 := by
    simp [th0, thetaPhys]
  linarith

/-- Canonical physical rear kinematics whose front is the marked unit-tangent
data above. -/
def terminalFrontKinematics
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (rear : Data)
    (hrear : ev rear = terminalCurve A)
    (hper : perim rear = terminalPeriod A)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) :
    PhysicalRearLimitKinematics kh rear (unitTangentData A) := by
  let d := normalizedTerminalSteering A
  have hd := deltaPhys_normalizedTerminalSteering A
  have htheta := thetaPhys_normalizedTerminalSteering A
  refine
    { theta0 := A.Theta Gamma.T 0
      steering := d
      sf := A.sf Gamma.T
      curvature_continuous := ?_
      arclength_rightInverse := ?_
      front_frenet := ?_
      rear_track := ?_
      rear_perimeter := ?_
      steering_nonzero := ?_ }
  · dsimp [d, normalizedTerminalSteering]
    exact normalizedTerminalCurvature_continuous A
  · intro x
    rw [hd]
    exact A.sf_rightInverse Gamma.T x
  · intro s
    rw [ev_unitTangentData, htheta]
    exact A.front_frenet Gamma.T s
  · intro x
    rw [hrear, ev_unitTangentData, hd, htheta]
    change terminalCurve A x = rearTrack (A.F Gamma.T)
      (A.Theta Gamma.T) (A.delta Gamma.T) (A.sf Gamma.T x)
    rfl
  · rw [hper, terminalPeriod, hd, unitTangentData_perim]
  · refine ⟨0, ?_⟩
    rw [hd]
    intro hz
    have hp := terminalCurvature_positive A hK0 0
    rw [terminalCurvature, hz, Real.tan_zero] at hp
    exact (lt_irrefl 0 hp)

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
