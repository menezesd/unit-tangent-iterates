import UnitTangentIterates.ConfiguredBaseExactSelectedDynamics
import UnitTangentIterates.RearOwnC1JacobiOfVelocitySpace
import UnitTangentIterates.RearOwnC1AngleCurvatureTimeSpatial

/-!
# Exact C1 transport before the final rear gauge flow

This module assembles every analytic witness of
`ConfiguredBaseProfiledResidualConstructor.Transport` except `anchor_flow`.
The latter is intentionally omitted: the front-phase reanchoring does not fix
the rear tangential drift.  A subsequent genuine rear gauge flow can shift
these explicit fields and then supply the anchor equation.
-/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseExactSelectedPreTransport

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  ConfiguredBaseExactSelectedDynamics
  RearOwnArclength RearOwnHigherRegularity RearOwnMixedOfInverseTimeSpatial
  RearOwnC1AngleCurvatureTimeSpatial

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

/-- Exact rear velocity in the inverse-arclength gauge. -/
abbrev rearVelocity (W : Output D Q n A) (S : ExactSelected (n := n) H) :
    ℝ → ℝ → ℂ :=
  RearOwnMixedOfInverseTimeSpatial.rearOwnVelocity
    (frontVelocity W) (frontAngleTime W) (steeringTime W S)
    (geometry W).Theta (deltaR W S) (sfR W S)

/-- Exact rear angle time field. -/
abbrev rearAngleTime (W : Output D Q n A) (S : ExactSelected (n := n) H) :
    ℝ → ℝ → ℝ :=
  RearOwnMixedOfInverseTimeSpatial.rearAngleTime
    (frontAngleTime W) (steeringTime W S) (deltaR W S) (sfR W S)

/-- Exact rear curvature time field. -/
abbrev rearCurvatureTime (W : Output D Q n A)
    (S : ExactSelected (n := n) H) : ℝ → ℝ → ℝ :=
  RearOwnC1AngleCurvatureTimeSpatial.rearCurvatureTime
    (steeringTime W S) (geometry W).K (deltaR W S) (sfR W S)

/-- Spatial derivative of the shifted front normal source. -/
def shiftedEtaS (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  fun t s ↦ ProfiledInterpolationFields.enS
    (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n)
    t (s + frontPhase W t)

/-- Spatial derivative of the rear Jacobi source. -/
def jacobiSpatial (W : Output D Q n A) (S : ExactSelected (n := n) H) :
    ℝ → ℝ → ℝ := fun t x ↦
  let s := sfR W S t x
  let d := deltaR W S t s
  shiftedEtaS W t s / Real.cos d ^ 2 +
    (geometry W).etaF t s * Real.sin d *
      ((geometry W).K t s - Real.sin d) / Real.cos d ^ 3

/-- All exact transport data which are independent of the final rear gauge
flow. -/
structure PreTransport (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) where
  Ydot : ℝ → ℝ → ℂ
  alphaT : ℝ → ℝ → ℝ
  kT : ℝ → ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  Ydot_continuous : Continuous (uncurry Ydot)
  gS_continuous : Continuous (uncurry gS)
  rear_time : ∀ t x, HasDerivAt (fun r ↦ rearR W S r x) (Ydot t x) t
  jacobi : ∀ t x, HasDerivAt
    (fun x' ↦ RearFamilyFrame.frameNormal Ydot (psiR W S) t x')
    (jacobiSource W S t x -
      RearFamilyFrame.frameNormal Ydot (psiR W S) t x) x
  gS_deriv : ∀ t x, HasDerivAt (jacobiSource W S t) (gS t x) x
  curvatureSpatial_deriv : ∀ t x,
    HasDerivAt (kappaR W S t) (curvatureSpatial W S t x) x
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ psiR W S r x) (alphaT t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ Real.tan (deltaR W S r (sfR W S r x))) (kT t x) t
  rear_angle_time_continuous : Continuous (uncurry alphaT)
  rear_curvature_time_continuous : Continuous (uncurry kT)
  rear_angle_time_spatial : ∀ t x, HasDerivAt (alphaT t) (kT t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (psiR W S r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (RearFamilyFrame.frameTangential Ydot (psiR W S) t y : ℂ) *
            Complex.exp (Complex.I * (psiR W S t y : ℂ)) +
        (RearFamilyFrame.frameNormal Ydot (psiR W S) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (psiR W S t y : ℂ)))) Z x

namespace PreTransport

/-- Once a later rear gauge flow supplies its anchor equation, the pretransport
is exactly the constructor's `Transport`. -/
def toTransport (P : PreTransport W H S)
    (hanchor : ∀ t, HasDerivAt
      (fun r ↦ anchorPhi W S.delta r 0)
      (-RearFamilyFrame.frameTangential P.Ydot (psiR W S) t
        (anchorPhi W S.delta t 0)) t) : Transport W H S where
  Ydot := P.Ydot
  alphaT := P.alphaT
  kT := P.kT
  gS := P.gS
  Ydot_continuous := P.Ydot_continuous
  gS_continuous := P.gS_continuous
  rear_time := P.rear_time
  anchor_flow := hanchor
  jacobi := P.jacobi
  gS_deriv := P.gS_deriv
  curvatureSpatial_deriv := P.curvatureSpatial_deriv
  rear_angle_time_deriv := P.rear_angle_time_deriv
  rear_curvature_time_deriv := P.rear_curvature_time_deriv
  rear_angle_time_continuous := P.rear_angle_time_continuous
  rear_curvature_time_continuous := P.rear_curvature_time_continuous
  rear_angle_time_spatial := P.rear_angle_time_spatial
  mixed := P.mixed

end PreTransport

section Assembly

variable (W : Output D Q n A) (S : ExactSelected (n := n) H)

theorem shiftedEtaS_deriv (t s : ℝ) :
    HasDerivAt ((geometry W).etaF t) (shiftedEtaS W t s) s := by
  have hshift : HasDerivAt (fun y : ℝ ↦ y + frontPhase W t) 1 s :=
    (hasDerivAt_id s).add_const (frontPhase W t)
  have h := (W.sourceCertificate.en_space t (s + frontPhase W t)).comp s hshift
  simpa [geometry, etaF, rawEtaF, shiftedEtaS,
    TimeDependentSpatialReanchoring.shift] using h

theorem rear_time (t x : ℝ) :
    HasDerivAt (fun r ↦ rearR W S r x) (rearVelocity W S t x) t :=
  hasDerivAt_rearOwn_time
    (geometry W).front_contDiff (geometry W).angle_contDiff
    (deltaR_contDiff W S) (sfR_contDiff W S)
    (geometry W).front_frenet (geometry W).angle_frenet
    (deltaR_steering W S) (frontVelocity_time W)
    (frontAngleTime_time W) (steeringTime_time W S) t x

theorem rear_angle_time_deriv (t x : ℝ) :
    HasDerivAt (fun r ↦ psiR W S r x) (rearAngleTime W S t x) t :=
  hasDerivAt_rearOwnAngle_time
    (geometry W).angle_contDiff (deltaR_contDiff W S) (sfR_contDiff W S)
    (geometry W).angle_frenet (deltaR_steering W S)
    (frontAngleTime_time W) (steeringTime_time W S) t x

theorem curvatureSpatial_deriv (t x : ℝ) :
    HasDerivAt (kappaR W S t) (curvatureSpatial W S t x) x := by
  have hd := (deltaR_steering W S t (sfR W S t x)).comp x (sfR_deriv W S t x)
  have ht := (Real.hasDerivAt_tan (deltaR_cos_ne_zero W S t (sfR W S t x))).comp x hd
  apply ht.congr_deriv
  simp only [kappaR, curvatureSpatial, Function.comp_def]
  field_simp [deltaR_cos_ne_zero W S t (sfR W S t x)]

theorem rear_curvature_time_deriv (t x : ℝ) :
    HasDerivAt
      (fun r ↦ Real.tan (deltaR W S r (sfR W S r x)))
      (rearCurvatureTime W S t x) t := by
  have hsft : HasDerivAt (fun r ↦ sfR W S r x)
      (partialTime (sfR W S) t x) t :=
    hasDerivAt_partialTime ((sfR_contDiff W S).differentiable (by norm_num)) t x
  have hd := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    ((deltaR_contDiff W S).differentiable (by norm_num)) hsft
  have hpt : partialTime (deltaR W S) t (sfR W S t x) =
      steeringTime W S t (sfR W S t x) :=
    (hasDerivAt_partialTime ((deltaR_contDiff W S).differentiable (by norm_num))
      t _).unique (steeringTime_time W S t _)
  have hpx : partialArc (deltaR W S) t (sfR W S t x) =
      (geometry W).K t (sfR W S t x) -
        Real.sin (deltaR W S t (sfR W S t x)) :=
    (hasDerivAt_partialArc ((deltaR_contDiff W S).differentiable (by norm_num))
      t _).unique (deltaR_steering W S t _)
  rw [hpt, hpx] at hd
  have ht := (Real.hasDerivAt_tan
    (deltaR_cos_ne_zero W S t (sfR W S t x))).comp t hd
  apply ht.congr_deriv
  simp only [rearCurvatureTime,
    RearOwnC1AngleCurvatureTimeSpatial.rearCurvatureTime, smul_eq_mul]
  ring

theorem rear_angle_time_spatial (t x : ℝ) :
    HasDerivAt (rearAngleTime W S t) (rearCurvatureTime W S t x) x :=
  RearOwnC1AngleCurvatureTimeSpatial.rearAngleTime_spatial
    (deltaR_contDiff W S) (sfR_contDiff W S)
    (steeringTime_time W S)
    (by
      have heq : steeringTime W S = partialTime (deltaR W S) := by
        funext a y
        exact (steeringTime_time W S a y).unique
          (hasDerivAt_partialTime
            ((deltaR_contDiff W S).differentiable (by norm_num)) a y)
      rw [heq]
      exact (contDiff_partialTime_self (n := 0) (deltaR_contDiff W S)).continuous)
    (frontAngleTime_spatial W) (steeringTime_spatial W S)
    (deltaR_steering W S) (sfR_deriv W S) (sfR_rightInverse W S)
    (deltaR_cos_ne_zero W S) t x

theorem rear_velocity_space (t x : ℝ) : HasDerivAt (rearVelocity W S t)
    (Complex.I * (rearAngleTime W S t x : ℂ) *
      Complex.exp (Complex.I * (psiR W S t x : ℂ))) x :=
  hasDerivAt_rearOwnVelocity_space
    (deltaR_contDiff W S) (sfR_contDiff W S)
    (geometry W).angle_frenet (deltaR_steering W S)
    (frontAngleTime_time W) (steeringTime_time W S)
    (by
      have heq : steeringTime W S = partialTime (deltaR W S) := by
        funext a y
        exact (steeringTime_time W S a y).unique
          (hasDerivAt_partialTime
            ((deltaR_contDiff W S).differentiable (by norm_num)) a y)
      rw [heq]
      exact (contDiff_partialTime_self (n := 0) (deltaR_contDiff W S)).continuous)
    (frontAngleTime_spatial W) (steeringTime_spatial W S)
    (sfR_deriv W S) (sfR_rightInverse W S) (deltaR_cos_ne_zero W S)
    (frontMixed W) t x

theorem jacobi (t x : ℝ) : HasDerivAt
    (fun y ↦ RearFamilyFrame.frameNormal (rearVelocity W S) (psiR W S) t y)
    (jacobiSource W S t x -
      RearFamilyFrame.frameNormal (rearVelocity W S) (psiR W S) t x) x :=
  RearOwnC1JacobiOfVelocitySpace.jacobi
    (deltaR_cos_ne_zero W S)
    (fun a s ↦ frontVelocity_normal W a s (deltaR W S a s))
    (rear_velocity_space W S) (psiR_spatial W S) t x

theorem gS_deriv (t x : ℝ) :
    HasDerivAt (jacobiSource W S t) (jacobiSpatial W S t x) x := by
  let s := sfR W S t x
  let d := deltaR W S t s
  have heta := (shiftedEtaS_deriv W t s).comp x (sfR_deriv W S t x)
  have hd := (deltaR_steering W S t s).comp x (sfR_deriv W S t x)
  have hc := hd.cos
  have hq := heta.div hc (deltaR_cos_ne_zero W S t s)
  apply hq.congr_deriv
  simp only [jacobiSource, jacobiSpatial, s, d, Function.comp_def]
  field_simp [deltaR_cos_ne_zero W S t s]
  ring

theorem mixed (t x : ℝ) : ∃ Z : ℂ,
    HasDerivAt (fun r ↦ Complex.exp (Complex.I * (psiR W S r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (RearFamilyFrame.frameTangential (rearVelocity W S) (psiR W S) t y : ℂ) *
            Complex.exp (Complex.I * (psiR W S t y : ℂ)) +
        (RearFamilyFrame.frameNormal (rearVelocity W S) (psiR W S) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (psiR W S t y : ℂ)))) Z x :=
  RearOwnMixedOfInverseTimeSpatial.mixed
    (deltaR_contDiff W S) (sfR_contDiff W S) (geometry W).angle_contDiff
    (geometry W).angle_frenet (deltaR_steering W S)
    (frontAngleTime_time W) (steeringTime_time W S)
    (by
      have heq : steeringTime W S = partialTime (deltaR W S) := by
        funext a y
        exact (steeringTime_time W S a y).unique
          (hasDerivAt_partialTime
            ((deltaR_contDiff W S).differentiable (by norm_num)) a y)
      rw [heq]
      exact (contDiff_partialTime_self (n := 0) (deltaR_contDiff W S)).continuous)
    (frontAngleTime_spatial W) (steeringTime_spatial W S)
    (sfR_deriv W S) (sfR_rightInverse W S) (deltaR_cos_ne_zero W S)
    (frontMixed W) t x

theorem rearVelocity_continuous : Continuous (uncurry (rearVelocity W S)) := by
  have hrearC := contDiff_one_rearOwn
    (geometry W).front_contDiff (geometry W).angle_contDiff
    (deltaR_contDiff W S) (sfR_contDiff W S)
  have heq : rearVelocity W S = partialTime (rearR W S) := by
    funext t x
    exact (rear_time W S t x).unique
      (hasDerivAt_partialTime (hrearC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hrearC).continuous

theorem rearAngleTime_continuous : Continuous (uncurry (rearAngleTime W S)) := by
  have heq : rearAngleTime W S = partialTime (psiR W S) := by
    funext t x
    exact (rear_angle_time_deriv W S t x).unique
      (hasDerivAt_partialTime
        ((psiR_contDiff W S).differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) (psiR_contDiff W S)).continuous

theorem rearCurvatureTime_continuous :
    Continuous (uncurry (rearCurvatureTime W S)) := by
  have hkC := rear_curvature_contDiff W S
  have heq : rearCurvatureTime W S =
      partialTime (fun t x ↦ Real.tan (deltaR W S t (sfR W S t x))) := by
    funext t x
    exact (rear_curvature_time_deriv W S t x).unique
      (hasDerivAt_partialTime (hkC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hkC).continuous

theorem shiftedEtaS_continuous : Continuous (uncurry (shiftedEtaS W)) := by
  let c := D.model.configs n
  have hk0 : Continuous (sourceK0 D n) := by
    simpa [c, sourceK0] using c.continuous_KP
  have hk1 : Continuous (sourceK1 D n) := by
    simpa [c, sourceK1] using c.continuous_kH
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (PathMetricCircle.B p.1, p.2 + frontPhase W p.1)) :=
    (PathMetricCircle.continuous_B.comp continuous_fst).prodMk
      (continuous_snd.add
        ((ConfiguredBaseInterpolationShiftedFront.phase_contDiff W).continuous.comp
          continuous_fst))
  have hnormal :=
    (InterpolationEstimate.continuous_uncurry_normalVelDeriv
      (θ₀ := D.model.thetaBase) (L := D.Hs n) hk0 hk1).comp hpair
  simpa [shiftedEtaS, ProfiledInterpolationFields.enS, uncurry] using
    (PathMetricCircle.continuous_w.comp continuous_fst).mul hnormal

theorem jacobiSpatial_continuous :
    Continuous (uncurry (jacobiSpatial W S)) := by
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, uncurry (sfR W S) p)) :=
    continuous_fst.prodMk (sfR_contDiff W S).continuous
  have hetaS := (shiftedEtaS_continuous W).comp hpair
  have heta := (etaF_continuous W).comp hpair
  have hK := (curvature_continuous W).comp hpair
  have hd := (deltaR_contDiff W S).continuous.comp hpair
  have hc := Real.continuous_cos.comp hd
  have hs := Real.continuous_sin.comp hd
  exact ((hetaS.div (hc.pow 2)
      (fun p ↦ pow_ne_zero 2 (deltaR_cos_ne_zero W S p.1 (sfR W S p.1 p.2)))).add
    (((heta.mul hs).mul (hK.sub hs)).div (hc.pow 3)
      (fun p ↦ pow_ne_zero 3
        (deltaR_cos_ne_zero W S p.1 (sfR W S p.1 p.2))))).congr
      (fun _ ↦ rfl)

/-- Exact configured transport prior to the genuine rear gauge flow. -/
def exact : PreTransport W H S where
  Ydot := rearVelocity W S
  alphaT := rearAngleTime W S
  kT := rearCurvatureTime W S
  gS := jacobiSpatial W S
  Ydot_continuous := rearVelocity_continuous W S
  gS_continuous := jacobiSpatial_continuous W S
  rear_time := rear_time W S
  jacobi := jacobi W S
  gS_deriv := gS_deriv W S
  curvatureSpatial_deriv := curvatureSpatial_deriv W S
  rear_angle_time_deriv := rear_angle_time_deriv W S
  rear_curvature_time_deriv := rear_curvature_time_deriv W S
  rear_angle_time_continuous := rearAngleTime_continuous W S
  rear_curvature_time_continuous := rearCurvatureTime_continuous W S
  rear_angle_time_spatial := rear_angle_time_spatial W S
  mixed := mixed W S

theorem exists_preTransport : Nonempty (PreTransport W H S) := ⟨exact W S⟩

end Assembly

end ConfiguredBaseExactSelectedPreTransport
