import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSuccessorFront
import UnitTangentIterates.RearOwnC1JacobiOfVelocitySpace
import UnitTangentIterates.RearOwnC1AngleCurvatureTimeSpatial
import UnitTangentIterates.RearOwnMixedOfInverseTimeSpatial

/-!
# Exact C1 successor transport for an arbitrary marking-aware source

The configured pretransport calculation is intrinsic.  This module states it
for the selected rear of any exact source, before the final tangential gauge
flow.  It uses only the source's retained C1, Jacobi, angle-time, and mixed
witnesses.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength
  RearOwnHigherRegularity RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor
  RearOwnMixedOfInverseTimeSpatial
  RearOwnC1AngleCurvatureTimeSpatial

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap : ℝ}
  (A : MarkingAwareSource Gamma P0 kh khat Qmax)

/-- A jointly C1 selected steering and inverse for the intrinsic successor
front. -/
structure ExactSelected where
  delta : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  periodic : ∀ t, Periodic (delta t) (period A t)
  strip_nonnegative : ∀ t s, 0 ≤ delta t s
  strip_le : ∀ t s, delta t s ≤ Real.arcsin kap
  steering : ∀ t s, HasDerivAt (delta t)
    (curvature A t s - Real.sin (delta t s)) s
  delta_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  sf_rightInverse : ∀ t x, rearArclength (delta t) (sf t x) = x
  sf_deriv : ∀ t x, HasDerivAt (sf t)
    (1 / Real.cos (delta t (sf t x))) x
  steeringTime_spatial : ∀ t s, HasDerivAt (partialTime delta t)
    (-Real.cos (delta t s) * partialTime delta t s + A.kT t s) s

namespace ExactSelected

variable {A} (S : ExactSelected A (kap := kap))

abbrev psi : ℝ → ℝ → ℝ := rearOwnAngle (angle A) S.delta S.sf
abbrev rear : ℝ → ℝ → ℂ := rearOwn (front A) (angle A) S.delta S.sf
abbrev kappa : ℝ → ℝ → ℝ :=
  fun t x => Real.tan (S.delta t (S.sf t x))
abbrev source : ℝ → ℝ → ℝ :=
  fun t x => rearNormal A t (S.sf t x) /
    Real.cos (S.delta t (S.sf t x))
abbrev curvatureSpatial : ℝ → ℝ → ℝ :=
  fun t x => (curvature A t (S.sf t x) -
      Real.sin (S.delta t (S.sf t x))) /
    Real.cos (S.delta t (S.sf t x)) ^ 3

theorem cos_ne_zero (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t s : ℝ) :
    Real.cos (S.delta t s) ≠ 0 :=
  ne_of_gt (SelectedPathData.cos_steering_pos hkap0 hkap1
    (S.strip_nonnegative t) (S.strip_le t) s)

theorem front_contDiff : ContDiff ℝ 1 (uncurry (front A)) :=
  contDiff_one_rearOwn A.front_contDiff A.angle_contDiff
    A.steering_contDiff A.sf_contDiff

theorem angle_contDiff : ContDiff ℝ 1 (uncurry (angle A)) := by
  have hpair : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      (z.1, uncurry A.sf z)) := contDiff_fst.prodMk A.sf_contDiff
  simpa [angle, rearOwnAngle, RearTrack.rearAngle, uncurry] using
    (A.angle_contDiff.comp hpair).sub (A.steering_contDiff.comp hpair)

theorem psi_contDiff : ContDiff ℝ 1 (uncurry (psi S)) := by
  have hpair : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      (z.1, uncurry S.sf z)) := contDiff_fst.prodMk S.sf_contDiff
  simpa [psi, rearOwnAngle, RearTrack.rearAngle, uncurry] using
    ((angle_contDiff (A := A)).comp hpair).sub (S.delta_contDiff.comp hpair)

theorem rear_contDiff : ContDiff ℝ 1 (uncurry (rear S)) :=
  contDiff_one_rearOwn (front_contDiff (A := A)) (angle_contDiff (A := A))
    S.delta_contDiff S.sf_contDiff

theorem kappa_contDiff (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    ContDiff ℝ 1 (uncurry (kappa S)) := by
  have hpair : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      (z.1, uncurry S.sf z)) := contDiff_fst.prodMk S.sf_contDiff
  have hd := S.delta_contDiff.comp hpair
  have hs := Real.contDiff_sin.comp hd
  have hc := Real.contDiff_cos.comp hd
  change ContDiff ℝ 1 (fun z : ℝ × ℝ =>
    Real.tan (S.delta z.1 (S.sf z.1 z.2)))
  simpa only [Real.tan_eq_sin_div_cos] using
    hs.div hc (fun z => cos_ne_zero S hkap0 hkap1 z.1 (S.sf z.1 z.2))

theorem psi_spatial (t x : ℝ) :
    HasDerivAt (psi S t) (kappa S t x) x :=
  RearOwnIsFront.hasDerivAt_rearOwnAngle
    (MarkingAwareSource.successorFrontCore A).angle_frenet
    S.steering S.sf_deriv t x

end ExactSelected

variable {A} (S : ExactSelected A (kap := kap))

abbrev steeringTime : ℝ → ℝ → ℝ := partialTime S.delta

abbrev rearVelocity : ℝ → ℝ → ℂ :=
  RearOwnMixedOfInverseTimeSpatial.rearOwnVelocity
    A.Ydot A.alphaT (steeringTime S) (angle A) S.delta S.sf

abbrev rearAngleTime : ℝ → ℝ → ℝ :=
  RearOwnMixedOfInverseTimeSpatial.rearAngleTime
    A.alphaT (steeringTime S) S.delta S.sf

abbrev rearCurvatureTime : ℝ → ℝ → ℝ :=
  RearOwnC1AngleCurvatureTimeSpatial.rearCurvatureTime
    (steeringTime S) (curvature A) S.delta S.sf

def jacobiSpatial : ℝ → ℝ → ℝ := fun t x =>
  let s := S.sf t x
  let d := S.delta t s
  deriv (rearNormal A t) s / Real.cos d ^ 2 +
    rearNormal A t s * Real.sin d *
      (curvature A t s - Real.sin d) / Real.cos d ^ 3

structure PreTransport where
  Ydot : ℝ → ℝ → ℂ
  alphaT : ℝ → ℝ → ℝ
  kT : ℝ → ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  Ydot_continuous : Continuous (uncurry Ydot)
  gS_continuous : Continuous (uncurry gS)
  rear_time : ∀ t x, HasDerivAt (fun r => S.rear r x) (Ydot t x) t
  jacobi : ∀ t x, HasDerivAt
    (frameNormal Ydot S.psi t)
    (S.source t x - frameNormal Ydot S.psi t x) x
  gS_deriv : ∀ t x, HasDerivAt (S.source t) (gS t x) x
  curvatureSpatial_deriv : ∀ t x,
    HasDerivAt (S.kappa t) (S.curvatureSpatial t x) x
  rear_angle_time_deriv : ∀ t x,
    HasDerivAt (fun r => S.psi r x) (alphaT t x) t
  rear_curvature_time_deriv : ∀ t x,
    HasDerivAt (fun r => S.kappa r x) (kT t x) t
  rear_angle_time_continuous : Continuous (uncurry alphaT)
  rear_curvature_time_continuous : Continuous (uncurry kT)
  rear_angle_time_spatial : ∀ t x, HasDerivAt (alphaT t) (kT t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (S.psi r x : ℂ))) Z t ∧
    HasDerivAt (fun y =>
      (frameTangential Ydot S.psi t y : ℂ) *
          Complex.exp (Complex.I * (S.psi t y : ℂ)) +
      (frameNormal Ydot S.psi t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (S.psi t y : ℂ)))) Z x

section Assembly

private theorem steeringTime_time (t s : ℝ) :
    HasDerivAt (fun r => S.delta r s) (steeringTime S t s) t :=
  hasDerivAt_partialTime (S.delta_contDiff.differentiable (by norm_num)) t s

private theorem steeringTime_continuous :
    Continuous (uncurry (steeringTime S)) :=
  (contDiff_partialTime_self (n := 0) S.delta_contDiff).continuous

theorem rear_time (t x : ℝ) :
    HasDerivAt (fun r => S.rear r x) (rearVelocity S t x) t :=
  hasDerivAt_rearOwn_time
    (ExactSelected.front_contDiff (A := A))
    (ExactSelected.angle_contDiff (A := A)) S.delta_contDiff S.sf_contDiff
    (MarkingAwareSource.successorFrontCore A).front_frenet
    (MarkingAwareSource.successorFrontCore A).angle_frenet S.steering
    A.rear_time_deriv A.rear_angle_time_deriv
    (steeringTime_time (A := A) S) t x

theorem rear_angle_time_deriv (t x : ℝ) :
    HasDerivAt (fun r => S.psi r x) (rearAngleTime S t x) t :=
  hasDerivAt_rearOwnAngle_time (ExactSelected.angle_contDiff (A := A))
    S.delta_contDiff S.sf_contDiff
    (MarkingAwareSource.successorFrontCore A).angle_frenet S.steering
    A.rear_angle_time_deriv (steeringTime_time (A := A) S) t x

theorem curvatureSpatial_deriv
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (S.kappa t) (S.curvatureSpatial t x) x := by
  have hd := (S.steering t (S.sf t x)).comp x (S.sf_deriv t x)
  have ht := (Real.hasDerivAt_tan
    (S.cos_ne_zero hkap0 hkap1 t (S.sf t x))).comp x hd
  apply ht.congr_deriv
  simp only [ExactSelected.kappa, ExactSelected.curvatureSpatial, Function.comp_def]
  field_simp [S.cos_ne_zero hkap0 hkap1 t (S.sf t x)]

theorem rear_curvature_time_deriv
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (fun r => S.kappa r x) (rearCurvatureTime S t x) t := by
  have hsft : HasDerivAt (fun r => S.sf r x) (partialTime S.sf t x) t :=
    hasDerivAt_partialTime (S.sf_contDiff.differentiable (by norm_num)) t x
  have hd := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (S.delta_contDiff.differentiable (by norm_num)) hsft
  have hpt : partialTime S.delta t (S.sf t x) =
      steeringTime S t (S.sf t x) := rfl
  have hpx : partialArc S.delta t (S.sf t x) =
      curvature A t (S.sf t x) - Real.sin (S.delta t (S.sf t x)) :=
    (hasDerivAt_partialArc (S.delta_contDiff.differentiable (by norm_num)) t _).unique
      (S.steering t _)
  rw [hpt, hpx] at hd
  have ht := (Real.hasDerivAt_tan
    (S.cos_ne_zero hkap0 hkap1 t (S.sf t x))).comp t hd
  apply ht.congr_deriv
  simp only [ExactSelected.kappa, rearCurvatureTime,
    RearOwnC1AngleCurvatureTimeSpatial.rearCurvatureTime, smul_eq_mul]
  ring

theorem rear_angle_time_spatial
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (rearAngleTime S t) (rearCurvatureTime S t x) x :=
  RearOwnC1AngleCurvatureTimeSpatial.rearAngleTime_spatial
    S.delta_contDiff S.sf_contDiff (steeringTime_time (A := A) S)
    (steeringTime_continuous (A := A) S)
    A.rear_angle_time_spatial S.steeringTime_spatial
    S.steering S.sf_deriv S.sf_rightInverse
    (S.cos_ne_zero hkap0 hkap1) t x

private theorem frontMixed (t x : ℝ) : ∃ Z : ℂ,
    HasDerivAt (fun r =>
      Complex.exp (Complex.I * (angle A r x : ℂ))) Z t ∧
    HasDerivAt (A.Ydot t) Z x := by
  obtain ⟨Z, htime, hspace⟩ := A.mixed_derivative t x
  refine ⟨Z, htime, ?_⟩
  have heq : (fun y =>
      (frameTangential A.Ydot (angle A) t y : ℂ) *
          Complex.exp (Complex.I * (angle A t y : ℂ)) +
      (frameNormal A.Ydot (angle A) t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (angle A t y : ℂ)))) =
      A.Ydot t := by
    funext y
    rw [← RearFamilyFrame.frame_reconstruct (A.Ydot t y) (angle A t y)]
    simp only [frameTangential, frameNormal]
    ring
  rw [← heq]
  exact hspace

theorem rear_velocity_space
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (rearVelocity S t)
      (Complex.I * (rearAngleTime S t x : ℂ) *
        Complex.exp (Complex.I * (S.psi t x : ℂ))) x :=
  hasDerivAt_rearOwnVelocity_space
    S.delta_contDiff S.sf_contDiff
    (MarkingAwareSource.successorFrontCore A).angle_frenet S.steering
    A.rear_angle_time_deriv (steeringTime_time (A := A) S)
    (steeringTime_continuous (A := A) S) A.rear_angle_time_spatial
    S.steeringTime_spatial
    S.sf_deriv S.sf_rightInverse (S.cos_ne_zero hkap0 hkap1)
    (frontMixed (A := A)) t x

private theorem frontNormal_eq (t s : ℝ) :
    frontNormalVelocityAt A.Ydot (angle A) S.delta t s = rearNormal A t s := by
  simp only [frontNormalVelocityAt, SelectedInverseJacobiODE.frontNormalVelocity,
    angle, rearNormal, rearOwnAngle, RearTrack.rearAngle, frameNormal]
  ring_nf
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem jacobi
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (frameNormal (rearVelocity S) S.psi t)
      (S.source t x - frameNormal (rearVelocity S) S.psi t x) x := by
  have H := RearOwnC1JacobiOfVelocitySpace.jacobi
    (S.cos_ne_zero hkap0 hkap1)
    (fun a s => frontNormal_eq (A := A) S a s)
    (rear_velocity_space (A := A) S hkap0 hkap1) S.psi_spatial t x
  simpa only [ExactSelected.source] using H

theorem gS_deriv
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (S.source t) (jacobiSpatial S t x) x := by
  let s := S.sf t x
  let d := S.delta t s
  have heta := (rearNormal_hasDeriv_deriv A t s).comp x (S.sf_deriv t x)
  have hd := (S.steering t s).comp x (S.sf_deriv t x)
  have hc := hd.cos
  have hq := heta.div hc (S.cos_ne_zero hkap0 hkap1 t s)
  apply hq.congr_deriv
  simp only [ExactSelected.source, jacobiSpatial, s, d, Function.comp_def]
  field_simp [S.cos_ne_zero hkap0 hkap1 t s]
  ring

theorem mixed
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) : ∃ Z : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (S.psi r x : ℂ))) Z t ∧
    HasDerivAt (fun y =>
      (frameTangential (rearVelocity S) S.psi t y : ℂ) *
          Complex.exp (Complex.I * (S.psi t y : ℂ)) +
      (frameNormal (rearVelocity S) S.psi t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (S.psi t y : ℂ)))) Z x :=
  RearOwnMixedOfInverseTimeSpatial.mixed
    S.delta_contDiff S.sf_contDiff (ExactSelected.angle_contDiff (A := A))
    (MarkingAwareSource.successorFrontCore A).angle_frenet S.steering
    A.rear_angle_time_deriv (steeringTime_time (A := A) S)
    (steeringTime_continuous (A := A) S) A.rear_angle_time_spatial
    S.steeringTime_spatial
    S.sf_deriv S.sf_rightInverse (S.cos_ne_zero hkap0 hkap1)
    (frontMixed (A := A)) t x

theorem rearVelocity_continuous : Continuous (uncurry (rearVelocity S)) := by
  have heq : rearVelocity S = partialTime S.rear := by
    funext t x
    exact (rear_time (A := A) S t x).unique
      (hasDerivAt_partialTime (S.rear_contDiff.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) S.rear_contDiff).continuous

theorem rearAngleTime_continuous : Continuous (uncurry (rearAngleTime S)) := by
  have heq : rearAngleTime S = partialTime S.psi := by
    funext t x
    exact (rear_angle_time_deriv (A := A) S t x).unique
      (hasDerivAt_partialTime (S.psi_contDiff.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) S.psi_contDiff).continuous

theorem rearCurvatureTime_continuous
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry (rearCurvatureTime S)) := by
  have heq : rearCurvatureTime S = partialTime S.kappa := by
    funext t x
    exact (rear_curvature_time_deriv (A := A) S hkap0 hkap1 t x).unique
      (hasDerivAt_partialTime
        ((S.kappa_contDiff hkap0 hkap1).differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0)
    (S.kappa_contDiff hkap0 hkap1)).continuous

theorem jacobiSpatial_continuous
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry (jacobiSpatial S)) := by
  have hpair : Continuous (fun z : ℝ × ℝ =>
      (z.1, uncurry S.sf z)) :=
    continuous_fst.prodMk S.sf_contDiff.continuous
  have hetaS := (rearNormal_deriv_joint_continuous A).comp hpair
  have heta := (by
    cases A.frame_regularity with
    | joint hY hpsi =>
        exact (RearOwnTangential.contDiff_frameNormal hY hpsi).continuous
    | spatial R => exact R.normal.continuous0 :
      Continuous (uncurry (rearNormal A))) |>.comp hpair
  have hK := A.rear_curvature_contDiff.continuous.comp hpair
  have hd := S.delta_contDiff.continuous.comp hpair
  have hc := Real.continuous_cos.comp hd
  have hs := Real.continuous_sin.comp hd
  exact ((hetaS.div (hc.pow 2)
      (fun z => pow_ne_zero 2 (S.cos_ne_zero hkap0 hkap1 z.1 (S.sf z.1 z.2)))).add
    (((heta.mul hs).mul (hK.sub hs)).div (hc.pow 3)
      (fun z => pow_ne_zero 3
        (S.cos_ne_zero hkap0 hkap1 z.1 (S.sf z.1 z.2))))).congr
      (fun _ => rfl)

def exact (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) : PreTransport S where
  Ydot := rearVelocity S
  alphaT := rearAngleTime S
  kT := rearCurvatureTime S
  gS := jacobiSpatial S
  Ydot_continuous := rearVelocity_continuous (A := A) S
  gS_continuous := jacobiSpatial_continuous (A := A) S hkap0 hkap1
  rear_time := rear_time (A := A) S
  jacobi := jacobi (A := A) S hkap0 hkap1
  gS_deriv := gS_deriv (A := A) S hkap0 hkap1
  curvatureSpatial_deriv := curvatureSpatial_deriv (A := A) S hkap0 hkap1
  rear_angle_time_deriv := rear_angle_time_deriv (A := A) S
  rear_curvature_time_deriv := rear_curvature_time_deriv (A := A) S hkap0 hkap1
  rear_angle_time_continuous := rearAngleTime_continuous (A := A) S
  rear_curvature_time_continuous := rearCurvatureTime_continuous (A := A) S hkap0 hkap1
  rear_angle_time_spatial := rear_angle_time_spatial (A := A) S hkap0 hkap1
  mixed := mixed (A := A) S hkap0 hkap1

end Assembly

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
