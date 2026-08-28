import UnitTangentIterates.ConfiguredBaseInterpolationMarkingAwareSourceResidual
import UnitTangentIterates.RearOwnFrameDriftReanchoring
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Reanchoring the profiled selected rear

The profiled interpolation is first constructed in its raw spatial gauge.  Its
configured marking has moving front phase `p(t)`.  Shifting the front by `p`
induces the rear-arclength phase

`q(t) = rearArclength (delta t) (p t)`.

This file records the simultaneous transport of the front geometry, selected
steering inverse, selected rear, and rear marking.  In particular, the shifted
inverse is `sf(t,x+q(t))-p(t)` and the normalized rear marking fixes zero.
-/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseProfiledSelectedRearReanchoring

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingAwareSourceResidual
  ConfiguredBaseInterpolationMarkingSource
  FiniteSmoothRearFamilyMarkingAwareSource

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}

abbrev rawF (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    ℝ → ℝ → ℂ :=
  ProfiledInterpolationFields.Y (sourceK0 D n) (sourceK1 D n)
    D.model.thetaBase (D.Hs n)

abbrev rawTheta (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.alpha (sourceK0 D n) (sourceK1 D n)
    D.model.thetaBase

abbrev rawK (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.kappa (sourceK0 D n) (sourceK1 D n)

abbrev rawEtaF (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.en (sourceK0 D n) (sourceK1 D n)
    D.model.thetaBase (D.Hs n)

abbrev rawPhi (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  ProfiledInterpolationFields.PhiB W.sourcePhi

/-- The moving phase of the configured front marking. -/
def frontPhase (W : Output D Q n A) (t : ℝ) : ℝ := rawPhi W t 0

/-- The front fields translated to the configured marked origin. -/
def F (W : Output D Q n A) : ℝ → ℝ → ℂ :=
  TimeDependentSpatialReanchoring.shift (rawF D n) (frontPhase W)

def Theta (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (rawTheta D n) (frontPhase W)

def K (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (rawK D n) (frontPhase W)

def etaF (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (rawEtaF D n) (frontPhase W)

/-- The raw nonaffine marking, normalized by its own moving phase. -/
def phi (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.normalize (rawPhi W) (frontPhase W)

abbrev phi1 (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  ConfiguredBaseInterpolationMarkingSource.phi1 W

abbrev phi2 (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  ConfiguredBaseInterpolationMarkingSource.phi2 W

@[simp] theorem frontPhase_eq_phase (W : Output D Q n A) :
    frontPhase W = ConfiguredBaseInterpolationMarkingSource.phase W := rfl

/-- The transported raw fields provide exactly the generalized front geometry
required by a configured residual source. -/
def geometry (W : Output D Q n A) : Geometry W := by
  let G := configuredGeometry W
  refine
    { F := F W
      Theta := Theta W
      K := K W
      etaF := etaF W
      phi := phi W
      phi1 := phi1 W
      phi2 := phi2 W
      front_frenet := ?_
      angle_frenet := ?_
      front_contDiff := ?_
      angle_contDiff := ?_
      front_periodic := ?_
      angle_periodic := ?_
      period_pos := G.period_pos
      eta_link := ?_
      phi_shift := ?_
      phi_deriv := ?_
      phi1_deriv := ?_
      phi1_continuous := G.phi1_continuous
      phi2_continuous := G.phi2_continuous
      etaF_bound := ?_
      curvature_abs_le_of_actual := ?_ }
  · simpa [F, rawF, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.front] using G.front_frenet
  · simpa [Theta, K, rawTheta, rawK, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.angle,
      ConfiguredBaseInterpolationShiftedFront.curvature] using G.angle_frenet
  · simpa [F, rawF, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.front] using G.front_contDiff
  · simpa [Theta, rawTheta, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.angle] using G.angle_contDiff
  · simpa [F, rawF, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.front] using G.front_periodic
  · simpa [Theta, rawTheta, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.angle] using G.angle_periodic
  · simpa [etaF, rawEtaF, phi, rawPhi, frontPhase,
      ConfiguredBaseInterpolationMarkingSource.etaF,
      ConfiguredBaseInterpolationMarkingSource.phi,
      TimeDependentSpatialReanchoring.shift,
      TimeDependentSpatialReanchoring.normalize] using
      (ConfiguredBaseInterpolationShiftedFront.certificate W).eta_link
  · simpa [phi, rawPhi, frontPhase,
      ConfiguredBaseInterpolationMarkingSource.phi,
      TimeDependentSpatialReanchoring.normalize] using G.phi_shift
  · simpa [phi, rawPhi, frontPhase,
      ConfiguredBaseInterpolationMarkingSource.phi,
      TimeDependentSpatialReanchoring.normalize] using G.phi_deriv
  · simpa using G.phi1_deriv
  · simpa [etaF, rawEtaF, frontPhase,
      ConfiguredBaseInterpolationMarkingSource.etaF,
      TimeDependentSpatialReanchoring.shift] using G.etaF_bound
  · intro H k hkh t s
    simpa [K, rawK, frontPhase,
      ConfiguredBaseInterpolationShiftedFront.curvature] using
      G.curvature_abs_le_of_actual H hkh t s

/-- Front phase measured in the selected rear's own arclength. -/
def rearPhase (W : Output D Q n A) (delta : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  rearArclength (delta t) (frontPhase W t)

/-- Steering translated by the moving front phase. -/
def deltaShift (W : Output D Q n A) (delta : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift delta (frontPhase W)

/-- Inverse selected rear coordinate after translating the front and rebasing
the rear origin. -/
def sfShift (W : Output D Q n A) (delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ sf t (x + rearPhase W delta t) - frontPhase W t

theorem rearPhase_contDiff (W : Output D Q n A) {delta : ℝ → ℝ → ℝ}
    (hdelta : ContDiff ℝ 1 (uncurry delta)) :
    ContDiff ℝ 1 (rearPhase W delta) := by
  have hA : ContDiff ℝ 1
      (uncurry fun t s ↦ rearArclength (delta t) s) :=
    RearOwnHigherRegularity.contDiff_rearArclengthFamily hdelta
  simpa [rearPhase, uncurry] using hA.comp
    (contDiff_id.prodMk (ConfiguredBaseInterpolationShiftedFront.phase_contDiff W))

theorem deltaShift_contDiff (W : Output D Q n A) {delta : ℝ → ℝ → ℝ}
    (hdelta : ContDiff ℝ 1 (uncurry delta)) :
    ContDiff ℝ 1 (uncurry (deltaShift W delta)) := by
  exact TimeDependentSpatialReanchoring.shift_contDiff hdelta
    (ConfiguredBaseInterpolationShiftedFront.phase_contDiff W)

theorem sfShift_contDiff (W : Output D Q n A) {delta sf : ℝ → ℝ → ℝ}
    (hdelta : ContDiff ℝ 1 (uncurry delta))
    (hsf : ContDiff ℝ 1 (uncurry sf)) :
    ContDiff ℝ 1 (uncurry (sfShift W delta sf)) := by
  have hq := rearPhase_contDiff W hdelta
  have hp := ConfiguredBaseInterpolationShiftedFront.phase_contDiff W
  have hpair : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      (p.1, p.2 + rearPhase W delta p.1)) :=
    contDiff_fst.prodMk (contDiff_snd.add (hq.comp contDiff_fst))
  simpa [sfShift, uncurry] using
    (hsf.comp hpair).sub (hp.comp contDiff_fst)

theorem deltaShift_periodic (W : Output D Q n A)
    {delta : ℝ → ℝ → ℝ} {P : ℝ → ℝ}
    (hper : ∀ t, Periodic (delta t) (P t)) (t : ℝ) :
    Periodic (deltaShift W delta t) (P t) :=
  TimeDependentSpatialReanchoring.shift_periodic hper t

theorem deltaShift_steering (W : Output D Q n A)
    {delta : ℝ → ℝ → ℝ}
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (rawK D n t s - Real.sin (delta t s)) s) (t s : ℝ) :
    HasDerivAt (deltaShift W delta t)
      (K W t s - Real.sin (deltaShift W delta t s)) s := by
  simpa [deltaShift, K, TimeDependentSpatialReanchoring.shift] using
    TimeDependentSpatialReanchoring.shift_spatial_deriv hsteer t s

theorem rearArclength_deltaShift (W : Output D Q n A)
    {delta : ℝ → ℝ → ℝ} (hdelta : ∀ t, Continuous (delta t)) (t s : ℝ) :
    rearArclength (deltaShift W delta t) s =
      rearArclength (delta t) (s + frontPhase W t) - rearPhase W delta t := by
  simpa [deltaShift, rearPhase, TimeDependentSpatialReanchoring.shift] using
    SelectedInverseShiftEquivariance.rearArclength_shift
      (hdelta t) (frontPhase W t) s

theorem sfShift_rightInverse (W : Output D Q n A)
    {delta sf : ℝ → ℝ → ℝ} (hdelta : ∀ t, Continuous (delta t))
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x) (t x : ℝ) :
    rearArclength (deltaShift W delta t) (sfShift W delta sf t x) = x := by
  rw [rearArclength_deltaShift W hdelta]
  simp only [sfShift]
  rw [show sf t (x + rearPhase W delta t) - frontPhase W t +
      frontPhase W t = sf t (x + rearPhase W delta t) by ring,
    hinv]
  ring

theorem sfShift_deriv (W : Output D Q n A)
    {delta sf : ℝ → ℝ → ℝ}
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x) (t x : ℝ) :
    HasDerivAt (sfShift W delta sf t)
      (1 / Real.cos (deltaShift W delta t (sfShift W delta sf t x))) x := by
  have hinner : HasDerivAt
      (fun y : ℝ ↦ y + rearPhase W delta t) 1 x :=
    (hasDerivAt_id x).add_const (rearPhase W delta t)
  have h := (hsf t (x + rearPhase W delta t)).scomp x hinner
  convert h.sub_const (frontPhase W t) using 1 <;>
    simp [sfShift, deltaShift, TimeDependentSpatialReanchoring.shift]

/-- Rear curves commute with the simultaneous front/rear reanchoring. -/
theorem rearOwn_shift (W : Output D Q n A) (delta sf : ℝ → ℝ → ℝ)
    (t x : ℝ) :
    RearOwnArclength.rearOwn (F W) (Theta W) (deltaShift W delta)
        (sfShift W delta sf) t x =
      RearOwnArclength.rearOwn (rawF D n) (rawTheta D n) delta sf t
        (x + rearPhase W delta t) := by
  simp [RearOwnArclength.rearOwn, RearTrack.rearTrack, RearTrack.rearAngle,
    F, Theta, deltaShift, sfShift, TimeDependentSpatialReanchoring.shift]

theorem rearOwnAngle_shift (W : Output D Q n A) (delta sf : ℝ → ℝ → ℝ)
    (t x : ℝ) :
    RearOwnArclength.rearOwnAngle (Theta W) (deltaShift W delta)
        (sfShift W delta sf) t x =
      RearOwnArclength.rearOwnAngle (rawTheta D n) delta sf t
        (x + rearPhase W delta t) := by
  simp [RearOwnArclength.rearOwnAngle, RearTrack.rearAngle,
    Theta, deltaShift, sfShift, TimeDependentSpatialReanchoring.shift]

/-- The raw front marking measured in rear arclength, normalized by the induced
rear phase.  This normalization fixes its coordinate origin, but it does not
assert the gauge-flow equation for the rear tangential field. -/
def anchorPhi (W : Output D Q n A) (delta : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.normalize
    (fun t u ↦ rearArclength (delta t) (rawPhi W t u))
    (rearPhase W delta)

@[simp] theorem anchorPhi_zero (W : Output D Q n A)
    (delta : ℝ → ℝ → ℝ) (t : ℝ) : anchorPhi W delta t 0 = 0 := by
  simp [anchorPhi, rearPhase, frontPhase,
    TimeDependentSpatialReanchoring.normalize]

/-- The normalized rear marking is equivalently obtained by applying the
shifted rear-arclength map to the normalized front marking. -/
theorem anchorPhi_eq_rearArclength (W : Output D Q n A)
    {delta : ℝ → ℝ → ℝ} (hdelta : ∀ t, Continuous (delta t)) (t u : ℝ) :
    anchorPhi W delta t u =
      rearArclength (deltaShift W delta t) (phi W t u) := by
  rw [rearArclength_deltaShift W hdelta]
  simp [anchorPhi, phi, TimeDependentSpatialReanchoring.normalize]

/-- Spatial normal-frame regularity is invariant under the induced rear
translation. -/
def normalSpatialC2 {rho : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 rho) (hq : Continuous q) :
    RearOwnFrameDrift.SpatialC2
      (TimeDependentSpatialReanchoring.shift rho q) :=
  S.shift hq

/-- The translated tangential field, pinned by subtracting its moving base
value, retains its spatial `C²` certificate and vanishes at zero. -/
def tangentialSpatialC2 {xi : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 xi) (hq : Continuous q) :
    RearOwnFrameDrift.SpatialC2
      (RearOwnFrameDrift.SpatialC2.tangentialReanchor xi q) :=
  RearOwnFrameDrift.SpatialC2.tangentialReanchorSpatialC2 S hq

@[simp] theorem tangential_reanchored_zero (xi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t : ℝ) :
    RearOwnFrameDrift.SpatialC2.tangentialReanchor xi q t 0 = 0 :=
  RearOwnFrameDrift.SpatialC2.tangentialReanchor_zero xi q t

end ConfiguredBaseProfiledSelectedRearReanchoring
