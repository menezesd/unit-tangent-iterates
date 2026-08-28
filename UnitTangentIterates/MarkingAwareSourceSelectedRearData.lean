import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.PinchedSliceData
import UnitTangentIterates.RearOwnTangential

/-! # The selected-rear endpoint Data intrinsic to a marking-aware source -/

noncomputable section

open Function MarkedSpace PathMetric RearOwnArclength RearTrack

namespace FiniteSmoothRearFamilyMarkingAwareSource

open FiniteSmoothRearFamilyMarkingAwareAppliedSource

namespace MarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

def selectedRearCurve (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦
  rearOwn A.F A.Theta A.delta A.sf t (rearPeriod A t * u)

def selectedRearVelocity (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦
  (rearPeriod A t : ℂ) * rearOwnTangent A.Theta A.delta A.sf t
    (rearPeriod A t * u)

def selectedRearAcceleration
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦
  ((rearPeriod A t ^ 2 *
      Real.tan (A.delta t (A.sf t (rearPeriod A t * u))) : ℝ) : ℂ) *
    (Complex.I * rearOwnTangent A.Theta A.delta A.sf t
      (rearPeriod A t * u))

private theorem curve_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (selectedRearCurve A t) (selectedRearVelocity A t u) u := by
  let L := rearPeriod A t
  have hscale : HasDerivAt (fun z : ℝ ↦ L * z) L u := by
    simpa using (hasDerivAt_id u).const_mul L
  have h := (RearOwnArclength.hasDerivAt_rearOwn_space
    A.front_frenet A.angle_frenet A.steering A.sf_deriv A.cos_ne_zero
    t (L * u)).scomp u hscale
  simpa [selectedRearCurve, selectedRearVelocity, L, mul_comm] using h

private theorem curve_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Periodic (selectedRearCurve A t) 1 := by
  intro u
  have hclose := RearOwnArclength.rearOwn_closing
    A.kh_nonnegative A.kh_lt_one
    (fun r ↦ Differentiable.continuous fun s ↦
      (A.steering r s).differentiableAt)
    A.strip_nonnegative A.strip_le A.steering_periodic A.sf_rightInverse
    A.front_periodic A.angle_periodic t (rearPeriod A t * u)
  simpa [selectedRearCurve, rearPeriod, mul_add] using hclose

private theorem velocity_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (selectedRearVelocity A t)
      (selectedRearAcceleration A t u) u := by
  let L := rearPeriod A t
  let psi := rearOwnAngle A.Theta A.delta A.sf t
  have hscale : HasDerivAt (fun z : ℝ ↦ L * z) L u := by
    simpa using (hasDerivAt_id u).const_mul L
  have hpsi := RearOwnTangential.hasDerivAt_rearOwnAngle_space
    A.angle_frenet A.steering A.sf_deriv t (L * u)
  have htau := (CurvatureInterpolation.hasDerivAt_tau (psi (L * u))).scomp
    (L * u) hpsi
  have hcomp := htau.scomp u hscale
  have h := hcomp.const_mul (L : ℂ)
  convert h using 1
  · funext y
    simp [selectedRearVelocity, rearOwnTangent,
      TwoCapPairsAssembly.tau_eq_exp, psi, L, mul_comm]
  · simp [selectedRearAcceleration, rearOwnTangent,
      TwoCapPairsAssembly.tau_eq_exp, Complex.ofReal_tan,
      psi, L, mul_assoc, mul_comm, mul_left_comm, pow_two]

private theorem acceleration_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Continuous (selectedRearAcceleration A t) := by
  have hv : Continuous (selectedRearVelocity A t) :=
    Differentiable.continuous fun u ↦ (velocity_deriv A t u).differentiableAt
  have hL : rearPeriod A t ≠ 0 := (A.rear_period_pos t).ne'
  have htangent : Continuous (fun u ↦
      rearOwnTangent A.Theta A.delta A.sf t (rearPeriod A t * u)) := by
    have heq : (fun u ↦ rearOwnTangent A.Theta A.delta A.sf t
        (rearPeriod A t * u)) =
        fun u ↦ ((rearPeriod A t : ℂ)⁻¹) * selectedRearVelocity A t u := by
      funext u
      simp [selectedRearVelocity, hL]
    rw [heq]
    exact continuous_const.mul hv
  have hkappa : Continuous (fun u ↦
      Real.tan (A.delta t (A.sf t (rearPeriod A t * u)))) := by
    have hs : Continuous (fun x ↦ Real.tan (A.delta t (A.sf t x))) := by
      simpa [uncurry] using A.rear_curvature_contDiff.continuous.comp
        (continuous_const.prodMk continuous_id)
    exact hs.comp (continuous_const.mul continuous_id)
  exact (Complex.continuous_ofReal.comp (continuous_const.mul hkappa)).mul
    (continuous_const.mul htangent)

/-- The selected rear at a fixed time, affinely marked by its own arclength
period.  Its stored velocity and acceleration are the exact spatial jets. -/
def selectedRearData (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : Data :=
  (PinchedPath.sliceBCF (selectedRearCurve A t)
      (Differentiable.continuous fun u ↦ (curve_deriv A t u).differentiableAt)
      (curve_periodic A t),
    PinchedPath.sliceBCF (selectedRearVelocity A t)
      (Differentiable.continuous fun u ↦ (velocity_deriv A t u).differentiableAt)
      (periodic_of_hasDerivAt (curve_deriv A t) (curve_periodic A t)),
    PinchedPath.sliceBCF (selectedRearAcceleration A t)
      (acceleration_continuous A t)
      (periodic_of_hasDerivAt (velocity_deriv A t)
        (periodic_of_hasDerivAt (curve_deriv A t) (curve_periodic A t))))

@[simp] theorem selectedRearData_curve
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (A.selectedRearData t).1 u = selectedRearCurve A t u := rfl

@[simp] theorem selectedRearData_velocity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (A.selectedRearData t).2.1 u = selectedRearVelocity A t u := rfl

theorem selectedRearData_perim
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    perim (A.selectedRearData t) = rearPeriod A t := by
  rw [perim, selectedRearData_velocity, selectedRearVelocity, norm_mul,
    RearOwnArclength.norm_rearOwn_tangent]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (A.rear_period_pos t)

theorem ev_selectedRearData
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    ev (A.selectedRearData t) x =
      rearOwn A.F A.Theta A.delta A.sf t x := by
  rw [ev, selectedRearData_curve, selectedRearCurve, selectedRearData_perim]
  have hL : rearPeriod A t ≠ 0 := by
    exact (A.rear_period_pos t).ne'
  have h : rearPeriod A t * (x / rearPeriod A t) = x := by
    calc
      rearPeriod A t * (x / rearPeriod A t) =
          (rearPeriod A t / rearPeriod A t) * x := by ring
      _ = x := by rw [div_self hL, one_mul]
  rw [h]

theorem selectedRearData_curve_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (⇑(A.selectedRearData t).1)
      ((A.selectedRearData t).2.1 u) u :=
  curve_deriv A t u

theorem selectedRearData_velocity_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (⇑(A.selectedRearData t).2.1)
      ((A.selectedRearData t).2.2 u) u :=
  velocity_deriv A t u

end MarkingAwareSource

end FiniteSmoothRearFamilyMarkingAwareSource
