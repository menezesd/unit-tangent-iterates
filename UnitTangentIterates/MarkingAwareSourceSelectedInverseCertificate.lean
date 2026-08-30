import UnitTangentIterates.MarkingAwareSourceSelectedRearData
import UnitTangentIterates.RearOwnIsFront
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.TubeMemberFloorFree

/-!
# The intrinsic marked selected-inverse certificate of a marking-aware source

At every time, a marking-aware source already stores all equations defining its
selected rear.  This file packages the naturally normalized front as `Data` and
assembles those equations into `SelectedInverseMap.IsMarkedSelectedInverse`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareSource

open FiniteSmoothRearFamilyMarkingAwareAppliedSource

namespace MarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-! ### The naturally normalized front datum at an arbitrary time -/

/-- The front curve at time `t`, normalized to have parameter period one. -/
def frontCurve (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦ A.F t (A.P t * u)

/-- The exact normalized-parameter velocity of `frontCurve`. -/
def frontVelocity (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦
  (A.P t : ℂ) * Complex.exp (Complex.I * (A.Theta t (A.P t * u) : ℂ))

/-- The exact normalized-parameter acceleration of `frontCurve`. -/
def frontAcceleration (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : ℝ → ℂ := fun u ↦
  ((A.P t : ℂ) ^ 2) *
    (Complex.I * (A.K t (A.P t * u) : ℂ) *
      Complex.exp (Complex.I * (A.Theta t (A.P t * u) : ℂ)))

private theorem frontCurvature_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Continuous (A.K t) := by
  have htheta : ContDiff ℝ 1 (A.Theta t) :=
    A.angle_contDiff.comp (contDiff_const.prodMk contDiff_id)
  have heq : deriv (A.Theta t) = A.K t :=
    funext fun s ↦ (A.angle_frenet t s).deriv
  rw [← heq]
  exact htheta.continuous_deriv (by norm_num)

theorem frontCurve_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (frontCurve A t) (frontVelocity A t u) u := by
  have hi : HasDerivAt (fun z : ℝ ↦ A.P t * z) (A.P t) u := by
    simpa using (hasDerivAt_id u).const_mul (A.P t)
  simpa [frontCurve, frontVelocity, smul_eq_mul, mul_comm] using
    (A.front_frenet t (A.P t * u)).scomp u hi

theorem frontVelocity_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    HasDerivAt (frontVelocity A t) (frontAcceleration A t u) u := by
  have hi : HasDerivAt (fun z : ℝ ↦ A.P t * z) (A.P t) u := by
    simpa using (hasDerivAt_id u).const_mul (A.P t)
  have htheta := (A.angle_frenet t (A.P t * u)).scomp u hi
  have h := (((htheta.ofReal_comp).const_mul Complex.I).cexp).const_mul
    (A.P t : ℂ)
  convert h using 1
  · simp only [frontAcceleration, smul_eq_mul, Function.comp_apply]
    push_cast
    ring

theorem frontCurve_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Periodic (frontCurve A t) 1 := by
  intro u
  simp only [frontCurve, mul_add, mul_one]
  exact A.front_periodic t (A.P t * u)

theorem frontVelocity_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Periodic (frontVelocity A t) 1 := by
  intro u
  simp only [frontVelocity, mul_add, mul_one]
  rw [A.angle_periodic t (A.P t * u)]
  have hcast : ((A.Theta t (A.P t * u) + 2 * Real.pi : ℝ) : ℂ) =
      (A.Theta t (A.P t * u) : ℂ) + 2 * Real.pi := by
    push_cast
    ring
  rw [hcast, mul_add, Complex.exp_add]
  have h2pi : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [show Complex.I * (2 * (Real.pi : ℂ)) =
      2 * Real.pi * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]

private theorem frontAcceleration_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Continuous (frontAcceleration A t) := by
  have hKc := frontCurvature_continuous A t
  have hThetac : Continuous (A.Theta t) :=
    A.angle_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact continuous_const.mul ((continuous_const.mul
    (Complex.continuous_ofReal.comp
      (hKc.comp (continuous_const.mul continuous_id)))).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (hThetac.comp (continuous_const.mul continuous_id))))))

/-- The exact fixed-time front `Data`: its normalized parameter has period one,
its speed and perimeter are `A.P t`, and its arclength evaluation is `A.F t`. -/
def frontData (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) : Data :=
  (PinchedPath.sliceBCF (frontCurve A t)
      (Differentiable.continuous fun u ↦
        (frontCurve_deriv A t u).differentiableAt)
      (frontCurve_periodic A t),
    PinchedPath.sliceBCF (frontVelocity A t)
      (Differentiable.continuous fun u ↦
        (frontVelocity_deriv A t u).differentiableAt)
      (frontVelocity_periodic A t),
    PinchedPath.sliceBCF (frontAcceleration A t)
      (frontAcceleration_continuous A t)
      (periodic_of_hasDerivAt (frontVelocity_deriv A t)
        (frontVelocity_periodic A t)))

@[simp] theorem frontData_curve
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (frontData A t).1 u = frontCurve A t u := rfl

@[simp] theorem frontData_velocity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (frontData A t).2.1 u = frontVelocity A t u := rfl

@[simp] theorem frontData_acceleration
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (frontData A t).2.2 u = frontAcceleration A t u := rfl

theorem frontData_perim
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    perim (frontData A t) = A.P t := by
  rw [perim, frontData_velocity]
  simp [frontVelocity, abs_of_pos (A.period_pos t)]

theorem ev_frontData
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    ev (frontData A t) = A.F t := by
  funext s
  rw [ev, frontData_curve, frontCurve, frontData_perim]
  field_simp [ne_of_gt (A.period_pos t)]

/-! ### The intrinsic tube witness for the selected rear -/

@[simp] theorem selectedRearData_acceleration
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    (A.selectedRearData t).2.2 u = selectedRearAcceleration A t u := rfl

theorem selectedRearData_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Periodic (⇑(A.selectedRearData t).1) 1 := by
  intro u
  have hclose := RearOwnArclength.rearOwn_closing
    A.kh_nonnegative A.kh_lt_one
    (fun r ↦ Differentiable.continuous fun s ↦
      (A.steering r s).differentiableAt)
    A.strip_nonnegative A.strip_le A.steering_periodic A.sf_rightInverse
    A.front_periodic A.angle_periodic t (rearPeriod A t * u)
  simpa [selectedRearCurve, rearPeriod, mul_add] using hclose

theorem selectedRearData_convex
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t u : ℝ) :
    0 ≤ ((starRingEnd ℂ) ((A.selectedRearData t).2.1 u) *
      (A.selectedRearData t).2.2 u).im := by
  simp only [selectedRearData_velocity, selectedRearData_acceleration]
  let z : ℂ := rearOwnTangent A.Theta A.delta A.sf t
    (rearPeriod A t * u)
  have hz : (starRingEnd ℂ) z * z = 1 := by
    dsimp [z, rearOwnTangent]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  have heq :
      (starRingEnd ℂ) (selectedRearVelocity A t u) *
          selectedRearAcceleration A t u =
        ((((rearPeriod A t) ^ 3 *
          Real.tan (A.delta t (A.sf t (rearPeriod A t * u))) : ℝ) : ℂ) *
          Complex.I) := by
    simp only [selectedRearVelocity, selectedRearAcceleration]
    rw [map_mul, Complex.conj_ofReal]
    change (rearPeriod A t : ℂ) * (starRingEnd ℂ) z *
        ((((rearPeriod A t) ^ 2 *
          Real.tan (A.delta t (A.sf t (rearPeriod A t * u))) : ℝ) : ℂ) *
          (Complex.I * z)) = _
    push_cast
    simp only [← Complex.ofReal_tan]
    linear_combination
      (((rearPeriod A t : ℂ) ^ 3 *
        (Real.tan (A.delta t (A.sf t (rearPeriod A t * u))) : ℂ) *
        Complex.I) * hz)
  rw [heq]
  simp only [Complex.mul_I_im, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg (A.rear_period_pos t).le 3)
    (RearOwnIsFront.rearOwn_curvature_nonneg A.kh_lt_one
      A.strip_nonnegative A.strip_le A.kh_nonnegative t
      (rearPeriod A t * u))

/-- The selected rear has exact constant speed `rearPeriod A t`.  A zero
curvature floor and zero chord constant give the unconditional tube witness
needed by `IsMarkedSelectedInverse`. -/
theorem selectedRearData_tube
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    IsTubeMember (rearPeriod A t) 0 0 (A.selectedRearData t) := by
  refine MarkedSpace.isTubeMember_zero_of_convex_and_chord
    (A.selectedRearData_curve_deriv t)
    (A.selectedRearData_velocity_deriv t)
    (selectedRearData_periodic A t) ?_ ?_ ?_ ?_
  · intro u v
    simp [selectedRearVelocity, RearOwnArclength.norm_rearOwn_tangent,
      abs_of_pos (A.rear_period_pos t)]
  · intro u
    rw [selectedRearData_velocity, selectedRearVelocity, norm_mul,
      RearOwnArclength.norm_rearOwn_tangent, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have habs : |rearPeriod A t| = rearPeriod A t :=
      abs_of_pos (A.rear_period_pos t)
    exact le_of_eq habs.symm
  · exact selectedRearData_convex A t
  · intro u _ v _
    simpa using norm_nonneg ((A.selectedRearData t).1 u -
      (A.selectedRearData t).1 v)

/-! ### The complete selected-inverse certificate -/

/-- Every fixed-time rear selected by a marking-aware source is unconditionally
the marked selected inverse of that source's exact fixed-time front datum. -/
theorem isMarkedSelectedInverse_selectedRearData
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    SelectedInverseMap.IsMarkedSelectedInverse kh (frontData A t)
      (A.selectedRearData t) := by
  refine ⟨⟨rearPeriod A t, 0, 0, selectedRearData_tube A t⟩,
    A.Theta t, A.K t, A.delta t, A.sf t,
    ?_, A.angle_frenet t, ?_, ?_, A.steering t,
    A.sf_rightInverse t, ?_, ?_⟩
  · intro s
    rw [ev_frontData]
    exact A.front_frenet t s
  · rw [frontData_perim]
    exact A.steering_periodic t
  · intro s
    exact ⟨A.strip_nonnegative t s, A.strip_le t s⟩
  · rw [selectedRearData_perim, frontData_perim, rearPeriod]
  · intro x
    rw [ev_selectedRearData, ev_frontData]
    rfl

end MarkingAwareSource

end FiniteSmoothRearFamilyMarkingAwareSource
