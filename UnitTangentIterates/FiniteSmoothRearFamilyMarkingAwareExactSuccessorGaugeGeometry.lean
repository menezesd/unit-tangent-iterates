import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Generic geometric reanchoring of an exact selected successor

A rear-arclength phase `q` corresponds to the front-arclength phase
`sigma(t) = sf(t,q(t))`.  This file transports the successor front and its
selected inverse through that phase without using configured interpolation
data.
-/

noncomputable section

open Function RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  (S : ExactSelected A (kap := kap))

def sigma (q : ℝ → ℝ) (t : ℝ) : ℝ := S.sf t (q t)

def F (q : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  TimeDependentSpatialReanchoring.shift (front A) (sigma S q)

def Theta (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (angle A) (sigma S q)

def K (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (curvature A) (sigma S q)

def etaF (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (rearNormal A) (sigma S q)

def phi (Phi : ℝ → ℝ → ℝ) (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.normalize Phi (sigma S q)

def delta (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift S.delta (sigma S q)

def sf (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => S.sf t (x + q t) - sigma S q t

theorem sigma_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (sigma S q) := by
  simpa [sigma, uncurry] using S.sf_contDiff.comp (contDiff_id.prodMk hq)

theorem front_frenet (q : ℝ → ℝ) (t s : ℝ) :
    HasDerivAt (F S q t)
      (Complex.exp (Complex.I * (Theta S q t s : ℂ))) s := by
  simpa [F, Theta] using TimeDependentSpatialReanchoring.shift_spatial_deriv
    (MarkingAwareSource.successorFrontCore A).front_frenet t s

theorem angle_frenet (q : ℝ → ℝ) (t s : ℝ) :
    HasDerivAt (Theta S q t) (K S q t s) s := by
  simpa [Theta, K] using TimeDependentSpatialReanchoring.shift_spatial_deriv
    (MarkingAwareSource.successorFrontCore A).angle_frenet t s

theorem front_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (F S q)) :=
  TimeDependentSpatialReanchoring.shift_contDiff
    (ExactSelected.front_contDiff (A := A)) (sigma_contDiff S hq)

theorem angle_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (Theta S q)) :=
  TimeDependentSpatialReanchoring.shift_contDiff
    (ExactSelected.angle_contDiff (A := A)) (sigma_contDiff S hq)

theorem front_periodic (q : ℝ → ℝ) (t s : ℝ) :
    F S q t (s + period A t) = F S q t s :=
  TimeDependentSpatialReanchoring.shift_periodic
    (MarkingAwareSource.successorFrontCore A).front_periodic t s

theorem angle_periodic (q : ℝ → ℝ) (t s : ℝ) :
    Theta S q t (s + period A t) = Theta S q t s + 2 * Real.pi :=
  TimeDependentSpatialReanchoring.shift_additive_periodic
    (MarkingAwareSource.successorFrontCore A).angle_periodic t s

theorem delta_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (delta S q)) :=
  TimeDependentSpatialReanchoring.shift_contDiff S.delta_contDiff
    (sigma_contDiff S hq)

theorem sf_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (uncurry (sf S q)) := by
  have hp : ContDiff ℝ 1 (fun z : ℝ × ℝ => (z.1, z.2 + q z.1)) :=
    contDiff_fst.prodMk (contDiff_snd.add (hq.comp contDiff_fst))
  simpa [sf, uncurry] using
    (S.sf_contDiff.comp hp).sub ((sigma_contDiff S hq).comp contDiff_fst)

theorem delta_periodic (q : ℝ → ℝ) (t : ℝ) :
    Periodic (delta S q t) (period A t) :=
  TimeDependentSpatialReanchoring.shift_periodic S.periodic t

theorem delta_strip_nonnegative (q : ℝ → ℝ) (t s : ℝ) :
    0 ≤ delta S q t s := S.strip_nonnegative t (s + sigma S q t)

theorem delta_strip_le (q : ℝ → ℝ) (t s : ℝ) :
    delta S q t s ≤ Real.arcsin kap := S.strip_le t (s + sigma S q t)

theorem steering (q : ℝ → ℝ) (t s : ℝ) :
    HasDerivAt (delta S q t)
      (K S q t s - Real.sin (delta S q t s)) s := by
  simpa [delta, K] using TimeDependentSpatialReanchoring.shift_spatial_deriv
    S.steering t s

theorem rearArclength_delta (q : ℝ → ℝ) (t s : ℝ) :
    rearArclength (delta S q t) s =
      rearArclength (S.delta t) (s + sigma S q t) - q t := by
  have hc : Continuous (S.delta t) := S.delta_contDiff.continuous.comp
    (continuous_const.prodMk continuous_id)
  have hi := S.sf_rightInverse t (q t)
  simpa [delta, TimeDependentSpatialReanchoring.shift, sigma, hi] using
    SelectedInverseShiftEquivariance.rearArclength_shift hc (sigma S q t) s

theorem sf_rightInverse (q : ℝ → ℝ) (t x : ℝ) :
    rearArclength (delta S q t) (sf S q t x) = x := by
  rw [rearArclength_delta S q]
  simp only [sf]
  rw [show S.sf t (x + q t) - sigma S q t + sigma S q t =
      S.sf t (x + q t) by ring, S.sf_rightInverse]
  ring

theorem sf_deriv (q : ℝ → ℝ) (t x : ℝ) :
    HasDerivAt (sf S q t)
      (1 / Real.cos (delta S q t (sf S q t x))) x := by
  have hi : HasDerivAt (fun y : ℝ => y + q t) 1 x :=
    (hasDerivAt_id x).add_const (q t)
  have h := (S.sf_deriv t (x + q t)).comp x hi
  convert h.sub_const (sigma S q t) using 1 <;>
    simp [sf, delta, sigma, TimeDependentSpatialReanchoring.shift]

theorem psi_eq_shift (q : ℝ → ℝ) (t x : ℝ) :
    rearOwnAngle (Theta S q) (delta S q) (sf S q) t x =
      TimeDependentSpatialReanchoring.shift S.psi q t x := by
  simp [rearOwnAngle, RearTrack.rearAngle, Theta, delta, sf, sigma,
    TimeDependentSpatialReanchoring.shift]

theorem rear_eq_shift (q : ℝ → ℝ) (t x : ℝ) :
    rearOwn (F S q) (Theta S q) (delta S q) (sf S q) t x =
      TimeDependentSpatialReanchoring.shift S.rear q t x := by
  simp [rearOwn, RearTrack.rearTrack, RearTrack.rearAngle, F, Theta, delta,
    sf, sigma, TimeDependentSpatialReanchoring.shift]

theorem kappa_eq_shift (q : ℝ → ℝ) (t x : ℝ) :
    Real.tan (delta S q t (sf S q t x)) =
      TimeDependentSpatialReanchoring.shift S.kappa q t x := by
  simp [delta, sf, sigma, TimeDependentSpatialReanchoring.shift]

theorem source_eq_shift (q : ℝ → ℝ) (t x : ℝ) :
    etaF S q t (sf S q t x) /
        Real.cos (delta S q t (sf S q t x)) =
      TimeDependentSpatialReanchoring.shift S.source q t x := by
  simp [etaF, delta, sf, sigma, ExactSelected.source,
    TimeDependentSpatialReanchoring.shift]

theorem curvatureSpatial_eq_shift (q : ℝ → ℝ) (t x : ℝ) :
    (K S q t (sf S q t x) - Real.sin (delta S q t (sf S q t x))) /
        Real.cos (delta S q t (sf S q t x)) ^ 3 =
      TimeDependentSpatialReanchoring.shift S.curvatureSpatial q t x := by
  simp [K, delta, sf, sigma, ExactSelected.curvatureSpatial,
    TimeDependentSpatialReanchoring.shift]

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
