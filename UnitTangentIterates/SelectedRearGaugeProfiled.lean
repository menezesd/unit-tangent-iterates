import Mathlib
import UnitTangentIterates.InterpolationFrenetProfiled
import UnitTangentIterates.RearOwnFrameDrift
import UnitTangentIterates.RearOwnTangential
import UnitTangentIterates.SelectedRearGaugeQualitative

/-!
# Stopped-clock profiles of canonical selected-rear data

The clock `PathMetricCircle.B` is only `C^1`, and its speed
`PathMetricCircle.w` is only continuous at the stopping times.  Consequently
the profiled rear velocity should not be advertised as jointly `C^2`.
This module retains exactly the regularity used by the marking-aware source:
joint `C^1` for unscaled fields and spatial `C^2` certificates for the two
scaled frame components.
-/

noncomputable section

open Function

namespace SelectedRearGaugeProfiled

open PathMetricCircle RearFamilyFrame RearOwnFrameDrift RearTrack
  RearOwnArclength RearOwnHigherRegularity

def profile {E : Type*} (f : ℝ → ℝ → E) : ℝ → ℝ → E :=
  fun t x ↦ f (B t) x

def profileRate (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ w t * f (B t) x

def profileVelocity (V : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun t x ↦ (w t : ℂ) * V (B t) x

/-- The stopped primitive is `C^1`, although its speed need not be
differentiable at the stopping times. -/
theorem contDiff_B : ContDiff ℝ 1 B := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hasDerivAt_B t).differentiableAt, ?_⟩
  have hderiv : deriv B = w := funext fun t ↦ (hasDerivAt_B t).deriv
  rw [hderiv]
  exact continuous_w

/-- Joint `C^1` regularity is preserved by the stopped clock. -/
theorem contDiff_profile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} (hf : ContDiff ℝ 1 (uncurry f)) :
    ContDiff ℝ 1 (uncurry (profile f)) := by
  have hp : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ (B p.1, p.2)) :=
    (contDiff_B.comp contDiff_fst).prodMk contDiff_snd
  simpa [profile, uncurry] using hf.comp hp

/-- Spatial derivatives are unchanged except for evaluation at the stopped
clock. -/
theorem hasDerivAt_profile_space {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f1 : ℝ → ℝ → E}
    (hf : ∀ a x, HasDerivAt (f a) (f1 a x) x) (t x : ℝ) :
    HasDerivAt (profile f t) (profile f1 t x) x :=
  hf (B t) x

/-- Time derivatives acquire the clock speed. -/
theorem hasDerivAt_profile_time {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f ft : ℝ → ℝ → E}
    (hf : ∀ a x, HasDerivAt (fun r ↦ f r x) (ft a x) a) (t x : ℝ) :
    HasDerivAt (fun r ↦ profile f r x) (w t • ft (B t) x) t := by
  exact (hf (B t) x).scomp t (hasDerivAt_B t)

theorem periodic_profile {f : ℝ → ℝ → ℝ} {P : ℝ → ℝ}
    (hf : ∀ a, Periodic (f a) (P a)) (t : ℝ) :
    Periodic (profile f t) (P (B t)) :=
  hf (B t)

/-- Raw canonical rear data before the stopped-clock substitution.  The
Jacobi source `g` is deliberately abstract: in applications it is the
transported front normal rate divided by the steering cosine. -/
structure RawData
    (Y Ydot : ℝ → ℝ → ℂ)
    (delta sf angle curvature alphaT kT g : ℝ → ℝ → ℝ) where
  delta_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  velocity_contDiff : ContDiff ℝ 2 (uncurry Ydot)
  angle_contDiff : ContDiff ℝ 2 (uncurry angle)
  curvature_contDiff : ContDiff ℝ 1 (uncurry curvature)
  rear_time : ∀ a x, HasDerivAt (fun r ↦ Y r x) (Ydot a x) a
  angle_time : ∀ a x, HasDerivAt (fun r ↦ angle r x) (alphaT a x) a
  curvature_time : ∀ a x,
    HasDerivAt (fun r ↦ curvature r x) (kT a x) a
  angle_time_continuous : Continuous (uncurry alphaT)
  curvature_time_continuous : Continuous (uncurry kT)
  angle_time_spatial : ∀ a x, HasDerivAt (alphaT a) (kT a x) x
  jacobi : ∀ a x, HasDerivAt (frameNormal Ydot angle a)
    (g a x - frameNormal Ydot angle a x) x
  mixed : ∀ a x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (angle r x : ℂ))) Z a ∧
    HasDerivAt
      (fun y ↦
        (frameTangential Ydot angle a y : ℂ) *
            Complex.exp (Complex.I * (angle a y : ℂ)) +
        (frameNormal Ydot angle a y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (angle a y : ℂ)))) Z x

/-- The weakened regularity and derivative package after profiling. -/
structure Data
    (Y Ydot : ℝ → ℝ → ℂ)
    (delta sf angle curvature alphaT kT g : ℝ → ℝ → ℝ) where
  delta_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  curvature_contDiff : ContDiff ℝ 1 (uncurry curvature)
  tangential_spatialC2 : SpatialC2 (frameTangential Ydot angle)
  normal_spatialC2 : SpatialC2 (frameNormal Ydot angle)
  rear_time : ∀ t x, HasDerivAt (fun r ↦ Y r x) (Ydot t x) t
  angle_time : ∀ t x, HasDerivAt (fun r ↦ angle r x) (alphaT t x) t
  curvature_time : ∀ t x,
    HasDerivAt (fun r ↦ curvature r x) (kT t x) t
  angle_time_continuous : Continuous (uncurry alphaT)
  curvature_time_continuous : Continuous (uncurry kT)
  angle_time_spatial : ∀ t x, HasDerivAt (alphaT t) (kT t x) x
  jacobi : ∀ t x, HasDerivAt (frameNormal Ydot angle t)
    (g t x - frameNormal Ydot angle t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (angle r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (frameTangential Ydot angle t y : ℂ) *
            Complex.exp (Complex.I * (angle t y : ℂ)) +
        (frameNormal Ydot angle t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (angle t y : ℂ)))) Z x

theorem frameTangential_profileVelocity (V : ℝ → ℝ → ℂ)
    (angle : ℝ → ℝ → ℝ) (t x : ℝ) :
    frameTangential (profileVelocity V) (profile angle) t x =
      w t * frameTangential V angle (B t) x := by
  simp [profileVelocity, profile, frameTangential]
  ring

theorem frameNormal_profileVelocity (V : ℝ → ℝ → ℂ)
    (angle : ℝ → ℝ → ℝ) (t x : ℝ) :
    frameNormal (profileVelocity V) (profile angle) t x =
      w t * frameNormal V angle (B t) x := by
  simp [profileVelocity, profile, frameNormal]
  ring

/-- Profile all canonical rear data through `B,w`.  The result is precisely
the differential block used by the residual marking-aware source. -/
def RawData.toProfiled
    {Y Ydot : ℝ → ℝ → ℂ}
    {delta sf angle curvature alphaT kT g : ℝ → ℝ → ℝ}
    (R : RawData Y Ydot delta sf angle curvature alphaT kT g) :
    Data (profile Y) (profileVelocity Ydot)
      (profile delta) (profile sf) (profile angle) (profile curvature)
      (profileRate alphaT) (profileRate kT) (profileRate g) := by
  have htan2 : ContDiff ℝ 2 (uncurry (frameTangential Ydot angle)) :=
    RearOwnFrameData.contDiff_frameTangential R.velocity_contDiff R.angle_contDiff
  have hnormal2 : ContDiff ℝ 2 (uncurry (frameNormal Ydot angle)) :=
    RearOwnTangential.contDiff_frameNormal R.velocity_contDiff R.angle_contDiff
  have htanS := SpatialC2.profile htan2 continuous_B continuous_w
  have hnormalS := SpatialC2.profile hnormal2 continuous_B continuous_w
  refine
    { delta_contDiff := contDiff_profile R.delta_contDiff
      sf_contDiff := contDiff_profile R.sf_contDiff
      curvature_contDiff := contDiff_profile R.curvature_contDiff
      tangential_spatialC2 := ?_
      normal_spatialC2 := ?_
      rear_time := ?_
      angle_time := ?_
      curvature_time := ?_
      angle_time_continuous := ?_
      curvature_time_continuous := ?_
      angle_time_spatial := ?_
      jacobi := ?_
      mixed := ?_ }
  · have heq : frameTangential (profileVelocity Ydot) (profile angle) =
        fun t x ↦ w t * frameTangential Ydot angle (B t) x := by
      funext t x
      exact frameTangential_profileVelocity Ydot angle t x
    rw [heq]
    exact htanS
  · have heq : frameNormal (profileVelocity Ydot) (profile angle) =
        fun t x ↦ w t * frameNormal Ydot angle (B t) x := by
      funext t x
      exact frameNormal_profileVelocity Ydot angle t x
    rw [heq]
    exact hnormalS
  · intro t x
    simpa [profileVelocity, profile, smul_eq_mul] using
      (hasDerivAt_profile_time R.rear_time t x)
  · intro t x
    simpa [profileRate, profile, smul_eq_mul] using
      (hasDerivAt_profile_time R.angle_time t x)
  · intro t x
    simpa [profileRate, profile, smul_eq_mul] using
      (hasDerivAt_profile_time R.curvature_time t x)
  · exact (continuous_w.comp continuous_fst).mul
      (R.angle_time_continuous.comp
        ((continuous_B.comp continuous_fst).prodMk continuous_snd))
  · exact (continuous_w.comp continuous_fst).mul
      (R.curvature_time_continuous.comp
        ((continuous_B.comp continuous_fst).prodMk continuous_snd))
  · intro t x
    exact (R.angle_time_spatial (B t) x).const_mul (w t)
  · intro t x
    have h := (R.jacobi (B t) x).const_mul (w t)
    have heq : frameNormal (profileVelocity Ydot) (profile angle) t =
        fun y ↦ w t * frameNormal Ydot angle (B t) y := by
      funext y
      exact frameNormal_profileVelocity Ydot angle t y
    rw [heq]
    convert h using 1 <;> simp [profileRate] <;> ring
  · intro t x
    obtain ⟨Z, hZt, hZx⟩ := R.mixed (B t) x
    refine ⟨(w t : ℂ) * Z, ?_, ?_⟩
    · simpa [profile] using hZt.scomp t (hasDerivAt_B t)
    · have h := hZx.const_mul (w t : ℂ)
      convert h using 1 <;>
        simp only [frameTangential_profileVelocity,
          frameNormal_profileVelocity]
      funext y
      simp only [profile]
      push_cast
      ring

/-! ### Canonical selected-rear adapter -/

/-- The unprofiled rear curve. -/
def canonicalRear (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℂ :=
  rearOwn F Theta delta sf

/-- The unprofiled rear tangent angle. -/
def canonicalAngle (Theta delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  rearOwnAngle Theta delta sf

/-- The unprofiled rear curvature. -/
def canonicalCurvature (delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ Real.tan (delta t (sf t x))

/-- The source in the inverse Jacobi equation. -/
def canonicalJacobiSource (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ :=
  fun t x ↦
    frontNormalVelocityAt (partialTime F) Theta delta t (sf t x) /
      Real.cos (delta t (sf t x))

@[simp] theorem profile_canonicalRear
    (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ) :
    profile (canonicalRear F Theta delta sf) =
      canonicalRear (profile F) (profile Theta) (profile delta) (profile sf) := by
  rfl

@[simp] theorem profile_canonicalAngle
    (Theta delta sf : ℝ → ℝ → ℝ) :
    profile (canonicalAngle Theta delta sf) =
      canonicalAngle (profile Theta) (profile delta) (profile sf) := by
  rfl

@[simp] theorem profile_canonicalCurvature
    (delta sf : ℝ → ℝ → ℝ) :
    profile (canonicalCurvature delta sf) =
      canonicalCurvature (profile delta) (profile sf) := by
  rfl

/-- Construct the raw differential package from the canonical selected rear.
The two existential fields are the canonical time derivatives of its angle
and curvature. -/
theorem exists_rawData
    {F : ℝ → ℝ → ℂ} {Theta delta K sf : ℝ → ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF3 : ContDiff ℝ (3 : ℕ) (uncurry F))
    (hTheta3 : ContDiff ℝ (3 : ℕ) (uncurry Theta))
    (hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta))
    (hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf))
    (hfront : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ∃ Ydot : ℝ → ℝ → ℂ, ∃ alphaT kT : ℝ → ℝ → ℝ,
      RawData (canonicalRear F Theta delta sf) Ydot delta sf
        (canonicalAngle Theta delta sf) (canonicalCurvature delta sf)
        alphaT kT (canonicalJacobiSource F Theta delta sf) := by
  obtain ⟨Ydot, hYtime, hYdot2, hang2, hcurv1, hjac⟩ :=
    SelectedRearGaugeQualitative.exists_canonical_gauge_jacobi_data
      (F := F) (Theta := Theta) (delta := delta) (K := K) (sf := sf) (kh := kh)
      hkh0 hkh1 hF3 hTheta3 hdelta4 hsf4 hfront hTheta hsteer
      hstrip0 hstrip1 hsfinv
  have hsfD : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x :=
    SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1
      hdelta4.continuous hstrip0 hstrip1 hsfinv
  obtain ⟨alphaT, kT, halphaT, hkT, halphaTc, hkTc, halphaTS⟩ :=
    SelectedRearGaugeQualitative.exists_canonical_angle_time_data
      hTheta hsteer hsfD hang2 hcurv1
  have hcos : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s ↦
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1
      (hstrip0 t) (hstrip1 t) s)
  have hYspace : ∀ t x, HasDerivAt (canonicalRear F Theta delta sf t)
      (Complex.exp (Complex.I * (canonicalAngle Theta delta sf t x : ℂ))) x :=
    fun t x ↦ hasDerivAt_rearOwn_space hfront hTheta hsteer hsfD hcos t x
  have htangent1 : ContDiff ℝ (1 : ℕ)
      (uncurry fun t x ↦
        Complex.exp (Complex.I * (canonicalAngle Theta delta sf t x : ℂ))) := by
    exact RearOwnTangential.contDiff_expI (hang2.of_le (by norm_num))
  have hY2 : ContDiff ℝ 2 (uncurry (canonicalRear F Theta delta sf)) := by
    have h := RearOwnTangential.contDiff_succ_of_partials
      (f := canonicalRear F Theta delta sf) (f1 := Ydot)
      (f2 := fun t x ↦
        Complex.exp (Complex.I * (canonicalAngle Theta delta sf t x : ℂ)))
      (n := 1) hYtime hYspace
      (hYdot2.of_le (by norm_num)) htangent1
    exact_mod_cast h
  have hmixed := SelectedRearGaugeQualitative.exists_mixed_frame_witness
    hY2 (hYdot2.of_le (by norm_num)) htangent1 hYspace hYtime
  exact ⟨Ydot, alphaT, kT,
    { delta_contDiff := hdelta4.of_le (by norm_num)
      sf_contDiff := hsf4.of_le (by norm_num)
      velocity_contDiff := hYdot2
      angle_contDiff := hang2
      curvature_contDiff := hcurv1
      rear_time := hYtime
      angle_time := halphaT
      curvature_time := hkT
      angle_time_continuous := halphaTc
      curvature_time_continuous := hkTc
      angle_time_spatial := halphaTS
      jacobi := hjac
      mixed := hmixed }⟩

/-- Selected-strip and inverse data retained alongside the weakened profiled
differential package. -/
structure ProfiledSelectedData
    (F : ℝ → ℝ → ℂ) (Theta delta K sf : ℝ → ℝ → ℝ)
    (P : ℝ → ℝ) (kh : ℝ)
    (Ydot : ℝ → ℝ → ℂ) (alphaT kT : ℝ → ℝ → ℝ) where
  core : Data
    (profile (canonicalRear F Theta delta sf)) (profileVelocity Ydot)
    (profile delta) (profile sf) (profile (canonicalAngle Theta delta sf))
    (profile (canonicalCurvature delta sf)) (profileRate alphaT) (profileRate kT)
    (profileRate (canonicalJacobiSource F Theta delta sf))
  strip_nonnegative : ∀ t s, 0 ≤ profile delta t s
  strip_le : ∀ t s, profile delta t s ≤ Real.arcsin kh
  steering : ∀ t s, HasDerivAt (profile delta t)
    (profile K t s - Real.sin (profile delta t s)) s
  sf_deriv : ∀ t x, HasDerivAt (profile sf t)
    (1 / Real.cos (profile delta t (profile sf t x))) x
  sf_rightInverse : ∀ t x,
    rearArclength (profile delta t) (profile sf t x) = x
  cos_ne_zero : ∀ t s, Real.cos (profile delta t s) ≠ 0
  steering_periodic : ∀ t, Periodic (profile delta t) (P (B t))

/-- End-to-end stopped-clock construction from a smooth raw selected rear. -/
theorem exists_profiled
    {F : ℝ → ℝ → ℂ} {Theta delta K sf : ℝ → ℝ → ℝ}
    {P : ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF3 : ContDiff ℝ (3 : ℕ) (uncurry F))
    (hTheta3 : ContDiff ℝ (3 : ℕ) (uncurry Theta))
    (hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta))
    (hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf))
    (hfront : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hperiodic : ∀ t, Periodic (delta t) (P t)) :
    ∃ Ydot : ℝ → ℝ → ℂ, ∃ alphaT kT : ℝ → ℝ → ℝ,
      Nonempty (ProfiledSelectedData F Theta delta K sf P kh Ydot alphaT kT) := by
  obtain ⟨Ydot, alphaT, kT, R⟩ := exists_rawData hkh0 hkh1 hF3 hTheta3
    hdelta4 hsf4 hfront hTheta hsteer hstrip0 hstrip1 hsfinv
  have hsfD : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x :=
    SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1
      hdelta4.continuous hstrip0 hstrip1 hsfinv
  refine ⟨Ydot, alphaT, kT, ⟨
    { core := R.toProfiled
      strip_nonnegative := fun t s ↦ hstrip0 (B t) s
      strip_le := fun t s ↦ hstrip1 (B t) s
      steering := ?_
      sf_deriv := ?_
      sf_rightInverse := ?_
      cos_ne_zero := ?_
      steering_periodic := fun t ↦ hperiodic (B t) }⟩⟩
  · intro t s
    exact hsteer (B t) s
  · intro t x
    exact hsfD (B t) x
  · intro t x
    exact hsfinv (B t) x
  · intro t s
    exact ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1
      (hstrip0 (B t)) (hstrip1 (B t)) s)

end SelectedRearGaugeProfiled
