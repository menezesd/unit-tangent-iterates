import UnitTangentIterates.ConfiguredBaseProfiledResidualConstructor
import UnitTangentIterates.RearOwnFrameGaugeFlowReanchoring

/-!
# Genuine selected-rear gauge reanchoring for the configured profile

Given a `C¹` rear phase `q`, its corresponding front-arclength phase is
`sigma(t) = sfR(t,q(t))`.  Translating the configured front fields by `sigma`
and the selected rear coordinate by `q` preserves every spatial selected-rear
identity.  This module contains only that geometric transport; the ODE and
time-frame transport are separate.
-/

noncomputable section

open Function RearTrack

namespace ConfiguredBaseProfiledSelectedRearGaugeReanchoring

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingAwareSourceResidual
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  RearOwnArclength

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

def sigma (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (t : ℝ) : ℝ := sfR W S t (q t)

def F (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  TimeDependentSpatialReanchoring.shift (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).F
    (sigma W S q)

def Theta (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).Theta
    (sigma W S q)

def K (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).K
    (sigma W S q)

def etaF (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).etaF
    (sigma W S q)

def phi (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.normalize
    (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).phi (sigma W S q)

def delta (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (deltaR W S) (sigma W S q)

def sf (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ sfR W S t (x + q t) - sigma W S q t

theorem sigma_contDiff (W : Output D Q n A) (S : ExactSelected (n := n) H)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (sigma W S q) := by
  simpa [sigma, uncurry] using (sfR_contDiff W S).comp
    (contDiff_id.prodMk hq)

/-- The fully shifted front geometry. -/
def geometry (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q) : Geometry W := by
  let G := ConfiguredBaseProfiledSelectedRearReanchoring.geometry W
  have hs := sigma_contDiff W S hq
  refine
    { F := F W S q
      Theta := Theta W S q
      K := K W S q
      etaF := etaF W S q
      phi := phi W S q
      phi1 := G.phi1
      phi2 := G.phi2
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
      phi1_deriv := G.phi1_deriv
      phi1_continuous := G.phi1_continuous
      phi2_continuous := G.phi2_continuous
      etaF_bound := ?_
      curvature_abs_le_of_actual := ?_ }
  · exact TimeDependentSpatialReanchoring.shift_spatial_deriv G.front_frenet
  · exact TimeDependentSpatialReanchoring.shift_spatial_deriv G.angle_frenet
  · exact TimeDependentSpatialReanchoring.shift_contDiff G.front_contDiff hs
  · exact TimeDependentSpatialReanchoring.shift_contDiff G.angle_contDiff hs
  · exact TimeDependentSpatialReanchoring.shift_periodic G.front_periodic
  · exact TimeDependentSpatialReanchoring.shift_additive_periodic G.angle_periodic
  · exact TimeDependentSpatialReanchoring.normalize_eta_link G.eta_link
  · exact TimeDependentSpatialReanchoring.normalize_shift G.phi_shift
  · exact TimeDependentSpatialReanchoring.normalize_spatial_deriv G.phi_deriv
  · intro t s
    exact G.etaF_bound t (s + sigma W S q t)
  · intro C k hk t s
    exact G.curvature_abs_le_of_actual C hk t (s + sigma W S q t)

theorem delta_contDiff (W : Output D Q n A) (S : ExactSelected (n := n) H)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (delta W S q)) :=
  TimeDependentSpatialReanchoring.shift_contDiff (deltaR_contDiff W S)
    (sigma_contDiff W S hq)

theorem sf_contDiff (W : Output D Q n A) (S : ExactSelected (n := n) H)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (sf W S q)) := by
  have hpair : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ (p.1, p.2 + q p.1)) :=
    contDiff_fst.prodMk (contDiff_snd.add (hq.comp contDiff_fst))
  simpa [sf, uncurry] using
    ((sfR_contDiff W S).comp hpair).sub
      ((sigma_contDiff W S hq).comp contDiff_fst)

theorem delta_periodic (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (t : ℝ) :
    Periodic (delta W S q t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) :=
  TimeDependentSpatialReanchoring.shift_periodic (deltaR_periodic W S) t

theorem delta_strip_nonnegative (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q : ℝ → ℝ) (t s : ℝ) :
    0 ≤ delta W S q t s :=
  deltaR_strip_nonnegative W S t (s + sigma W S q t)

theorem delta_strip_le (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q : ℝ → ℝ) (t s : ℝ) :
    delta W S q t s ≤ Real.arcsin H.k0 :=
  deltaR_strip_le W S t (s + sigma W S q t)

theorem delta_steering (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q) (t s : ℝ) :
    HasDerivAt (delta W S q t)
      ((geometry W S q hq).K t s - Real.sin (delta W S q t s)) s := by
  simpa [delta, geometry, K] using
    TimeDependentSpatialReanchoring.shift_spatial_deriv
      (deltaR_steering W S) t s

theorem rearArclength_delta (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q : ℝ → ℝ) (t s : ℝ) :
    rearArclength (delta W S q t) s =
      rearArclength (deltaR W S t) (s + sigma W S q t) - q t := by
  have hcont : Continuous (deltaR W S t) :=
    (deltaR_contDiff W S).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hsigma := sfR_rightInverse W S t (q t)
  simpa [delta, TimeDependentSpatialReanchoring.shift, sigma, hsigma] using
    SelectedInverseShiftEquivariance.rearArclength_shift
      hcont (sigma W S q t) s

theorem sf_rightInverse (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (t x : ℝ) :
    rearArclength (delta W S q t) (sf W S q t x) = x := by
  rw [rearArclength_delta W S q]
  simp only [sf]
  rw [show sfR W S t (x + q t) - sigma W S q t + sigma W S q t =
      sfR W S t (x + q t) by ring, sfR_rightInverse]
  ring

theorem sf_deriv (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (t x : ℝ) :
    HasDerivAt (sf W S q t)
      (1 / Real.cos (delta W S q t (sf W S q t x))) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ y + q t) 1 x :=
    (hasDerivAt_id x).add_const (q t)
  have h := (sfR_deriv W S t (x + q t)).comp x hinner
  convert h.sub_const (sigma W S q t) using 1 <;>
    simp [sf, delta, sigma, TimeDependentSpatialReanchoring.shift]

theorem psi_eq_shift (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q) (t x : ℝ) :
    rearOwnAngle (geometry W S q hq).Theta (delta W S q) (sf W S q) t x =
      TimeDependentSpatialReanchoring.shift (psiR W S) q t x := by
  simp [rearOwnAngle, RearTrack.rearAngle, geometry, Theta, delta, sf, sigma,
    TimeDependentSpatialReanchoring.shift]

theorem rearOwn_eq_shift (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q) (t x : ℝ) :
    rearOwn (geometry W S q hq).F (geometry W S q hq).Theta
        (delta W S q) (sf W S q) t x =
      TimeDependentSpatialReanchoring.shift (rearR W S) q t x := by
  simp [rearOwn, RearTrack.rearTrack, RearTrack.rearAngle, geometry, F, Theta,
    delta, sf, sigma, TimeDependentSpatialReanchoring.shift]

theorem kappa_eq_shift (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (q : ℝ → ℝ) (t x : ℝ) :
    Real.tan (delta W S q t (sf W S q t x)) =
      TimeDependentSpatialReanchoring.shift (kappaR W S) q t x := by
  simp [delta, sf, sigma, TimeDependentSpatialReanchoring.shift]

theorem jacobiSource_eq_shift (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q : ℝ → ℝ)
    (hq : ContDiff ℝ 1 q) (t x : ℝ) :
    (geometry W S q hq).etaF t (sf W S q t x) /
        Real.cos (delta W S q t (sf W S q t x)) =
      TimeDependentSpatialReanchoring.shift (jacobiSource W S) q t x := by
  simp [geometry, etaF, delta, sf, sigma, jacobiSource,
    TimeDependentSpatialReanchoring.shift]

theorem curvatureSpatial_eq_shift (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q : ℝ → ℝ)
    (hq : ContDiff ℝ 1 q) (t x : ℝ) :
    ((geometry W S q hq).K t (sf W S q t x) -
          Real.sin (delta W S q t (sf W S q t x))) /
        Real.cos (delta W S q t (sf W S q t x)) ^ 3 =
      TimeDependentSpatialReanchoring.shift (curvatureSpatial W S) q t x := by
  simp [geometry, K, delta, sf, sigma, curvatureSpatial,
    TimeDependentSpatialReanchoring.shift]

end ConfiguredBaseProfiledSelectedRearGaugeReanchoring
