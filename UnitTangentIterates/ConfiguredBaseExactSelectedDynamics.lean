import UnitTangentIterates.ConfiguredBaseProfiledResidualConstructor
import UnitTangentIterates.RearOwnMixedOfInverseTimeSpatial

/-!
# Canonical time field of the exact configured selected steering
-/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseExactSelectedDynamics

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  RearOwnHigherRegularity SteeringArclengthJointC1

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

/-- The canonical parameter derivative retained by joint `C¹` regularity. -/
def deltaTime (S : ExactSelected (D := D) (n := n) H) : ℝ → ℝ → ℝ :=
  partialTime S.delta

theorem deltaTime_time
    (S : ExactSelected (D := D) (n := n) H) (t s : ℝ) :
    HasDerivAt (fun r ↦ S.delta r s) (deltaTime S t s) t :=
  hasDerivAt_partialTime (S.delta_contDiff.differentiable (by norm_num)) t s

theorem deltaTime_continuous
    (S : ExactSelected (D := D) (n := n) H) :
    Continuous (uncurry (deltaTime S)) := by
  exact (contDiff_partialTime_self (n := 0) S.delta_contDiff).continuous

private theorem curvatureTime_continuous
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A) :
    Continuous (uncurry
      (ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n)) := by
  simpa [ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime,
    ProfiledInterpolationFields.kT, uncurry] using
    W.sourceCertificate.kT_cont

private theorem curvatureTime_periodic
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A) (t : ℝ) :
    Periodic (ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n t)
      (2 * D.Hs n) := by
  have hper0 : Periodic (sourceK0 D n) (2 * D.Hs n) := by
    simpa [two_mul] using (D.model.configs n).periodic_KP.add_period
      (D.model.configs n).periodic_KP
  have hper1 : Periodic (sourceK1 D n) (2 * D.Hs n) := by
    simpa [sourceK1, two_mul] using (D.model.configs n).periodic_kH.add_period
      (D.model.configs n).periodic_kH
  intro s
  simp only [ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime]
  rw [hper0 s, hper1 s]

theorem deltaTime_eq_arcVariation
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
    (S : ExactSelected (D := D) (n := n) H) (t s : ℝ) :
    deltaTime S t s =
      arcVariation
        (ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n)
        S.delta (2 * D.Hs n) t s := by
  obtain ⟨Klip, CK, hCK, hLip, hTaylor⟩ :=
    ConfiguredBaseProfiledSelectedSteeringC1.exists_time_bounds H n
  have hP : 0 < 2 * D.Hs n :=
    mul_pos (by norm_num) (D.model.separation_pos n)
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hparam := hasDerivAt_param_arc
    (K := rawK D n)
    (Kd := ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n)
    (delta := S.delta) (P := 2 * D.Hs n) (kap := H.k0)
    hP hk0 H.k0_lt_one (curvatureTime_continuous W)
    S.steering S.periodic
    (fun a y ↦ ⟨S.strip_nonnegative a y, S.strip_le a y⟩)
    (curvatureTime_periodic W) (by
      simpa [rawK, ProfiledInterpolationFields.kappa,
        CurvatureInterpolation.kappaInterp,
        ConfiguredBaseProfiledSelectedSteeringC1.curvature] using hLip)
    (by
      simpa [rawK, ProfiledInterpolationFields.kappa,
        CurvatureInterpolation.kappaInterp,
        ConfiguredBaseProfiledSelectedSteeringC1.curvature] using hTaylor)
    hCK t s
  exact (deltaTime_time S t s).unique hparam

/-- The canonical time field satisfies the exact Green spatial ODE. -/
theorem deltaTime_spatial
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
    (S : ExactSelected (D := D) (n := n) H) (t s : ℝ) :
    HasDerivAt (deltaTime S t)
      (-Real.cos (S.delta t s) * deltaTime S t s +
        ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n t s) s := by
  have hP : 0 < 2 * D.Hs n :=
    mul_pos (by norm_num) (D.model.separation_pos n)
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hgreen := hasDerivAt_arcVariation
    (K := rawK D n)
    (Kd := ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n)
    (delta := S.delta) (P := 2 * D.Hs n) (kap := H.k0)
    hP hk0 H.k0_lt_one (curvatureTime_continuous W)
    S.steering (fun a y ↦ ⟨S.strip_nonnegative a y, S.strip_le a y⟩)
    S.periodic (curvatureTime_periodic W) t s
  have heq : deltaTime S t =
      arcVariation
        (ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime D n)
        S.delta (2 * D.Hs n) t := by
    funext y
    exact deltaTime_eq_arcVariation W S t y
  rw [heq]
  simpa [← deltaTime_eq_arcVariation W S t s] using hgreen

section Shifted

variable (W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A)
  (S : ExactSelected (D := D) (n := n) H)

abbrev rawAngleTime : ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.alphaT (sourceK0 D n) (sourceK1 D n)

abbrev rawCurvatureTime : ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.kT (sourceK0 D n) (sourceK1 D n)

abbrev rawCurvatureSpatial : ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.kX (sourceK0' D n) (sourceK1' D n)

def rawFrontVelocity : ℝ → ℝ → ℂ := fun t s ↦
  ((-ProfiledInterpolationFields.h (sourceK0 D n) (sourceK1 D n)
      D.model.thetaBase (D.Hs n) t s : ℝ) : ℂ) *
      Complex.exp (Complex.I * (rawTheta D n t s : ℂ)) +
    (rawEtaF D n t s : ℂ) *
      (Complex.I * Complex.exp (Complex.I * (rawTheta D n t s : ℂ)))

def frontVelocity : ℝ → ℝ → ℂ := fun t s ↦
  rawFrontVelocity (D := D) (n := n) t (s + frontPhase W t) +
    (ConfiguredBaseInterpolationShiftedFront.phaseRate W t : ℂ) *
      Complex.exp (Complex.I * ((geometry W).Theta t s : ℂ))

def frontAngleTime : ℝ → ℝ → ℝ := fun t s ↦
  rawAngleTime (D := D) (n := n) t (s + frontPhase W t) +
    ConfiguredBaseInterpolationShiftedFront.phaseRate W t * (geometry W).K t s

def frontCurvatureTime : ℝ → ℝ → ℝ := fun t s ↦
  rawCurvatureTime (D := D) (n := n) t (s + frontPhase W t) +
    ConfiguredBaseInterpolationShiftedFront.phaseRate W t *
      rawCurvatureSpatial (D := D) (n := n) t (s + frontPhase W t)

def steeringTime : ℝ → ℝ → ℝ := fun t s ↦
  deltaTime S t (s + frontPhase W t) +
    ConfiguredBaseInterpolationShiftedFront.phaseRate W t *
      (rawK D n t (s + frontPhase W t) -
        Real.sin (S.delta t (s + frontPhase W t)))

include W in
theorem rawFrontVelocity_time (t s : ℝ) :
    HasDerivAt (fun r ↦ rawF D n r s)
      (rawFrontVelocity (D := D) (n := n) t s) t := by
  simpa [rawFrontVelocity, rawF, rawTheta, rawEtaF] using
    W.sourceCertificate.motion t s

theorem frontVelocity_time (t s : ℝ) :
    HasDerivAt (fun r ↦ (geometry W).F r s) (frontVelocity W t s) t := by
  have hmove := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (W.sourceCertificate.Y_C1.differentiable (by norm_num))
    ((hasDerivAt_const t s).add
      (ConfiguredBaseInterpolationShiftedFront.phase_hasDerivAt W t))
  have hpt : partialTime (rawF D n) t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      rawFrontVelocity (D := D) (n := n) t
        (s + ConfiguredBaseInterpolationMarkingSource.phase W t) :=
    (hasDerivAt_partialTime
      (W.sourceCertificate.Y_C1.differentiable (by norm_num)) t _).unique
      (rawFrontVelocity_time W t _)
  have hpx : partialArc (rawF D n) t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      Complex.exp (Complex.I * (rawTheta D n t
        (s + ConfiguredBaseInterpolationMarkingSource.phase W t) : ℂ)) :=
    (hasDerivAt_partialArc
      (W.sourceCertificate.Y_C1.differentiable (by norm_num)) t _).unique
      (W.sourceCertificate.tangent t _)
  simp only [Pi.add_apply, zero_add] at hmove
  rw [hpt, hpx] at hmove
  convert hmove using 1 <;>
    simp [geometry, F, Theta, rawF, rawTheta, frontPhase_eq_phase W,
      TimeDependentSpatialReanchoring.shift, frontVelocity,
      Complex.real_smul] <;> ring

theorem frontAngleTime_time (t s : ℝ) :
    HasDerivAt (fun r ↦ (geometry W).Theta r s) (frontAngleTime W t s) t := by
  have hmove := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (W.sourceCertificate.angle_C1.differentiable (by norm_num))
    ((hasDerivAt_const t s).add
      (ConfiguredBaseInterpolationShiftedFront.phase_hasDerivAt W t))
  have hpt : partialTime (rawTheta D n) t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      rawAngleTime (D := D) (n := n) t
        (s + ConfiguredBaseInterpolationMarkingSource.phase W t) :=
    (hasDerivAt_partialTime
      (W.sourceCertificate.angle_C1.differentiable (by norm_num)) t _).unique
      (W.sourceCertificate.angle_time t _)
  have hpx : partialArc (rawTheta D n) t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      rawK D n t (s + ConfiguredBaseInterpolationMarkingSource.phase W t) :=
    (hasDerivAt_partialArc
      (W.sourceCertificate.angle_C1.differentiable (by norm_num)) t _).unique
      (W.sourceCertificate.angle_space t _)
  simp only [Pi.add_apply, zero_add] at hmove
  rw [hpt, hpx] at hmove
  convert hmove using 1 <;>
    simp [geometry, Theta, K, rawTheta, rawK, frontPhase_eq_phase W,
      TimeDependentSpatialReanchoring.shift, frontAngleTime,
      smul_eq_mul]

theorem steeringTime_time (t s : ℝ) :
    HasDerivAt (fun r ↦ deltaR W S r s) (steeringTime W S t s) t := by
  have hmove := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (S.delta_contDiff.differentiable (by norm_num))
    ((hasDerivAt_const t s).add
      (ConfiguredBaseInterpolationShiftedFront.phase_hasDerivAt W t))
  have hpt : partialTime S.delta t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      deltaTime S t (s + ConfiguredBaseInterpolationMarkingSource.phase W t) := rfl
  have hpx : partialArc S.delta t
      (s + ConfiguredBaseInterpolationMarkingSource.phase W t) =
      rawK D n t (s + ConfiguredBaseInterpolationMarkingSource.phase W t) -
        Real.sin (S.delta t
          (s + ConfiguredBaseInterpolationMarkingSource.phase W t)) :=
    (hasDerivAt_partialArc
      (S.delta_contDiff.differentiable (by norm_num)) t _).unique
      (S.steering t _)
  simp only [Pi.add_apply, zero_add] at hmove
  rw [hpt, hpx] at hmove
  convert hmove using 1 <;>
    simp [deltaR, deltaShift, TimeDependentSpatialReanchoring.shift,
      steeringTime, frontPhase_eq_phase W, smul_eq_mul]

theorem frontAngleTime_spatial (t s : ℝ) :
    HasDerivAt (frontAngleTime W t) (frontCurvatureTime W t s) s := by
  have hshift : HasDerivAt (fun y : ℝ ↦ y + frontPhase W t) 1 s :=
    (hasDerivAt_id s).add_const (frontPhase W t)
  have h1 := (W.sourceCertificate.alphaT_space t (s + frontPhase W t)).scomp s hshift
  have h2 := (W.sourceCertificate.kappa_space t (s + frontPhase W t)).scomp s hshift
  have h := h1.add (h2.const_mul (ConfiguredBaseInterpolationShiftedFront.phaseRate W t))
  convert h using 1 <;>
    simp [frontAngleTime, frontCurvatureTime, geometry, K, rawK,
      rawAngleTime, rawCurvatureTime, rawCurvatureSpatial, frontPhase,
      TimeDependentSpatialReanchoring.shift,
      ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime,
      ProfiledInterpolationFields.kT] <;> ring

theorem steeringTime_spatial (t s : ℝ) :
    HasDerivAt (steeringTime W S t)
      (-Real.cos (deltaR W S t s) * steeringTime W S t s +
        frontCurvatureTime W t s) s := by
  have hshift : HasDerivAt (fun y : ℝ ↦ y + frontPhase W t) 1 s :=
    (hasDerivAt_id s).add_const (frontPhase W t)
  have h1 := (deltaTime_spatial W S t (s + frontPhase W t)).scomp s hshift
  have hK := (W.sourceCertificate.kappa_space t (s + frontPhase W t)).scomp s hshift
  have hd := (S.steering t (s + frontPhase W t)).scomp s hshift
  have hsin := hd.sin
  have hfield := hK.sub hsin
  have h := h1.add
    (hfield.const_mul (ConfiguredBaseInterpolationShiftedFront.phaseRate W t))
  convert h using 1 <;>
    simp [steeringTime, frontCurvatureTime, deltaR, deltaShift,
      TimeDependentSpatialReanchoring.shift, geometry, K, rawK,
      rawCurvatureTime, rawCurvatureSpatial, frontPhase,
      ConfiguredBaseProfiledSelectedSteeringC1.curvatureTime,
      ProfiledInterpolationFields.kT] <;> ring

theorem frontMixed (t s : ℝ) : ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * ((geometry W).Theta r s : ℂ))) Z t ∧
    HasDerivAt (frontVelocity W t) Z s := by
  obtain ⟨Z0, hZ0t, hZ0s⟩ := W.sourceCertificate.mixed_expanded
    t (s + frontPhase W t)
  have hshift : HasDerivAt (fun y : ℝ ↦ y + frontPhase W t) 1 s :=
    (hasDerivAt_id s).add_const (frontPhase W t)
  have hrawS := hZ0s.scomp s hshift
  have hangS := (W.sourceCertificate.angle_space t
    (s + frontPhase W t)).scomp s hshift
  have htanS := ((hangS.ofReal_comp.const_mul Complex.I).cexp)
  let Z := Complex.I * (frontAngleTime W t s : ℂ) *
    Complex.exp (Complex.I * ((geometry W).Theta t s : ℂ))
  refine ⟨Z, ?_, ?_⟩
  · have h := ((frontAngleTime_time W t s).ofReal_comp.const_mul Complex.I).cexp
    convert h using 1 <;> simp [Z] <;> ring
  · have hadd := hrawS.add
      (htanS.const_mul
        (ConfiguredBaseInterpolationShiftedFront.phaseRate W t : ℂ))
    have hZ0 : Z0 = Complex.I *
        (rawAngleTime (D := D) (n := n) t (s + frontPhase W t) : ℂ) *
        Complex.exp (Complex.I * (rawTheta D n t (s + frontPhase W t) : ℂ)) := by
      have he := ((W.sourceCertificate.angle_time t
        (s + frontPhase W t)).ofReal_comp.const_mul Complex.I).cexp
      exact hZ0t.unique (by convert he using 1 <;> ring)
    rw [hZ0] at hadd
    convert hadd using 1 <;>
      simp [frontVelocity, frontAngleTime, geometry, Theta, K, rawTheta, rawK,
        frontPhase_eq_phase W, TimeDependentSpatialReanchoring.shift, Z] <;> ring

/-- The exact shifted front velocity has the prescribed normal component,
independently of the steering angle used to express the rear frame. -/
theorem frontVelocity_normal (t s d : ℝ) :
    SelectedInverseJacobiODE.frontNormalVelocity (frontVelocity W t s)
      ((geometry W).Theta t s - d) d = (geometry W).etaF t s := by
  let theta := rawTheta D n t (s + frontPhase W t)
  let a := -ProfiledInterpolationFields.h (sourceK0 D n) (sourceK1 D n)
      D.model.thetaBase (D.Hs n) t (s + frontPhase W t) +
    ConfiguredBaseInterpolationShiftedFront.phaseRate W t
  let e := rawEtaF D n t (s + frontPhase W t)
  let E := Complex.exp (Complex.I * (theta : ℂ))
  have hvel : frontVelocity W t s = (a : ℂ) * E + (e : ℂ) * (Complex.I * E) := by
    simp [frontVelocity, rawFrontVelocity, a, e, E, theta, geometry, Theta,
      rawTheta, TimeDependentSpatialReanchoring.shift]
    ring
  have hang : (geometry W).Theta t s = theta := by
    rfl
  have heta : (geometry W).etaF t s = e := by
    rfl
  rw [hvel, hang, heta]
  simp only [SelectedInverseJacobiODE.frontNormalVelocity]
  rw [show theta - d + d = theta by ring]
  have hunit : E * (starRingEnd ℂ) E = 1 := by
    exact RearSmoothDependence.exp_mul_conj theta
  simp only [map_mul, Complex.conj_I]
  have hcalc :
      ((a : ℂ) * E + (e : ℂ) * (Complex.I * E)) *
          (-Complex.I * (starRingEnd ℂ) E) =
        (e : ℂ) - Complex.I * (a : ℂ) := by
    calc
      _ = ((e : ℂ) - Complex.I * (a : ℂ)) *
          (E * (starRingEnd ℂ) E) := by
            ring_nf
            simp only [Complex.I_sq]
            ring
      _ = (e : ℂ) - Complex.I * (a : ℂ) := by rw [hunit, mul_one]
  rw [hcalc]
  simp

end Shifted

end ConfiguredBaseExactSelectedDynamics
