import UnitTangentIterates.ConfiguredBaseInterpolationMarkingSource
import UnitTangentIterates.ConfiguredActualSubunitCurvature

/-!
# The correctly based intrinsic front for the configured interpolation

The interpolation gauge flow is not based at zero.  Its marked coordinate is
therefore normalized by subtracting `PhiB t 0`, and the intrinsic front must be
translated by the same amount in its spatial variable.  This file records the
geometric identities before the selected-rear construction.  In particular it
does not replace the genuine nonaffine marking by the legacy affine marking.
-/

noncomputable section

open Function

namespace ConfiguredBaseInterpolationShiftedFront

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingSource

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}

abbrev k0 : ℝ → ℝ := sourceK0 D n
abbrev k1 : ℝ → ℝ := sourceK1 D n

/-- The intrinsic front after moving the spatial origin to the gauge marking. -/
def front (W : Output D Q n A) (t s : ℝ) : ℂ :=
  ProfiledInterpolationFields.Y (k0 (D := D) (n := n))
    (k1 (D := D) (n := n)) D.model.thetaBase (D.Hs n) t
    (s + phase W t)

/-- The correspondingly based tangent angle. -/
def angle (W : Output D Q n A) (t s : ℝ) : ℝ :=
  ProfiledInterpolationFields.alpha (k0 (D := D) (n := n))
    (k1 (D := D) (n := n)) D.model.thetaBase t (s + phase W t)

/-- The correspondingly based curvature. -/
def curvature (W : Output D Q n A) (t s : ℝ) : ℝ :=
  ProfiledInterpolationFields.kappa (k0 (D := D) (n := n))
    (k1 (D := D) (n := n)) t (s + phase W t)

/-- The common spatial period of the intrinsic fronts. -/
def period (_W : Output D Q n A) (_t : ℝ) : ℝ := 2 * D.Hs n

/-- Velocity of the moving spatial origin. -/
def phaseRate (W : Output D Q n A) (t : ℝ) : ℝ :=
  ProfiledInterpolationFields.h (k0 (D := D) (n := n))
    (k1 (D := D) (n := n)) D.model.thetaBase (D.Hs n) t (phase W t)

/-- The phase-normalized front and marking data that are discharged directly
from the retained configured interpolation certificate. -/
structure Certificate (W : Output D Q n A) : Prop where
  front_frenet : ∀ t s, HasDerivAt (front W t)
    (Complex.exp (Complex.I * (angle W t s : ℂ))) s
  angle_frenet : ∀ t s, HasDerivAt (angle W t) (curvature W t s) s
  curvature_periodic : ∀ t, Periodic (curvature W t) (period W t)
  angle_closing : ∀ t s,
    angle W t (s + period W t) = angle W t s + 2 * Real.pi
  period_pos : ∀ t, 0 < period W t
  eta_link : ∀ t u,
    W.increment.eta t u = etaF W t (phi W t u)
  marking_zero : ∀ t, phi W t 0 = 0
  marking_shift : ∀ t u, phi W t (u + 1) = phi W t u + period W t
  marking_deriv : ∀ t u, HasDerivAt (phi W t)
    ((markingCertificate W).phi1 t u) u
  marking_second_deriv : ∀ t u,
    HasDerivAt ((markingCertificate W).phi1 t)
      ((markingCertificate W).phi2 t u) u
  marking_first_continuous : ∀ t,
    Continuous ((markingCertificate W).phi1 t)
  marking_second_continuous : ∀ t,
    Continuous ((markingCertificate W).phi2 t)
  eta_bound : ∀ t s, |etaF W t s| ≤ W.increment.m t

theorem certificate (W : Output D Q n A) : Certificate W := by
  let M := markingCertificate W
  refine
    { front_frenet := ?_
      angle_frenet := ?_
      curvature_periodic := ?_
      angle_closing := ?_
      period_pos := ?_
      eta_link := M.eta_link
      marking_zero := by
        intro t
        simp [M, markingCertificate, ConfiguredBaseInterpolationMarkingSource.phi,
          ConfiguredBaseInterpolationMarkingSource.phase]
      marking_shift := ?_
      marking_deriv := by
        intro t u
        exact M.deriv t u
      marking_second_deriv := by
        intro t u
        exact M.deriv2 t u
      marking_first_continuous := by
        intro t
        exact M.phi1_continuous t
      marking_second_continuous := by
        intro t
        exact M.phi2_continuous t
      eta_bound := by
        exact M.etaF_bound (fun _ => mul_pos (by norm_num)
          (D.separation_zero_pos.trans_le (D.separation_lower n))) }
  · intro t s
    have hs : HasDerivAt (fun x : ℝ => x + phase W t) 1 s :=
      (hasDerivAt_id s).add_const (phase W t)
    simpa [front, angle] using
      (W.sourceCertificate.tangent t (s + phase W t)).scomp s hs
  · intro t s
    have hs : HasDerivAt (fun x : ℝ => x + phase W t) 1 s :=
      (hasDerivAt_id s).add_const (phase W t)
    simpa [angle, curvature] using
      (W.sourceCertificate.angle_space t (s + phase W t)).scomp s hs
  · intro t s
    convert W.sourceCertificate.kappa_periodic t (s + phase W t) using 1 <;>
      simp [curvature, period] <;> ring
  · intro t s
    convert W.sourceCertificate.angle_closing t (s + phase W t) using 1 <;>
      simp [angle, period] <;> ring
  · intro t
    exact mul_pos (by norm_num)
      (D.separation_zero_pos.trans_le (D.separation_lower n))
  · intro t u
    simpa [markingCertificate, period] using M.shift t u

/-- The curvature ceiling of the shifted intrinsic front is the actual model
ceiling, not the coarse path-cost constant `D.kstar`. -/
theorem curvature_abs_le_of_actual
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    {kh : ℝ} (hkh : H.k0 ≤ kh) (t s : ℝ) :
    |curvature W t s| ≤ kh := by
  have h0nn : ∀ x, 0 ≤ sourceK0 D n x := by
    intro x
    simpa only [sourceK0, ← D.model.curvature_eq n] using
      H.front_nonnegative n x
  have h0le : ∀ x, sourceK0 D n x ≤ H.k0 := by
    intro x
    simpa only [sourceK0, ← D.model.curvature_eq n] using H.front_le n x
  have h1nn : ∀ x, 0 ≤ sourceK1 D n x := by
    intro x
    simpa only [sourceK1] using H.rear_nonnegative n x
  have h1le : ∀ x, sourceK1 D n x ≤ H.k0 := by
    intro x
    simpa only [sourceK1] using H.rear_le n x
  have hB := ProfiledInterpolationFields.B_mem_Icc t
  have hnonneg : 0 ≤ curvature W t s := by
    rw [curvature, ProfiledInterpolationFields.kappa,
      CurvatureInterpolation.kappaInterp]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hB.2) (h0nn _))
      (mul_nonneg hB.1 (h1nn _))
  rw [abs_of_nonneg hnonneg]
  exact (CurvatureInterpolation.kappaInterp_le h0le h1le hB
    (s + phase W t)).trans hkh

/-- Spatial closure is unchanged by the moving choice of origin. -/
theorem front_periodic (W : Output D Q n A) (t s : ℝ) :
    front W t (s + period W t) = front W t s := by
  let c := D.model.configs n
  have hk0c : Continuous (sourceK0 D n) := by
    simpa [c, sourceK0] using c.continuous_KP
  have hk1c : Continuous (sourceK1 D n) := by
    simpa [c, sourceK1] using c.continuous_kH
  have hper0 : Periodic (sourceK0 D n) (D.Hs n) := by
    simpa [c, sourceK0] using c.periodic_KP
  have hper1 : Periodic (sourceK1 D n) (D.Hs n) := by
    simpa [c, sourceK1] using c.periodic_kH
  have htot0 : (∫ r in (0 : ℝ)..D.Hs n, sourceK0 D n r) = Real.pi := by
    simpa [c, sourceK0] using c.integral_KP_eq_pi
  have htot1 : (∫ r in (0 : ℝ)..D.Hs n, sourceK1 D n r) = Real.pi := by
    simpa [c, sourceK1] using c.integral_kH_eq_pi
  have hp : Periodic
      (CurvatureInterpolation.interpCurve
        (CurvatureInterpolation.kappaInterp (sourceK0 D n) (sourceK1 D n)
          (PathMetricCircle.B t)) D.model.thetaBase (D.Hs n))
      (2 * D.Hs n) :=
    CurvatureInterpolation.interpCurve_periodic
      (θ₀ := D.model.thetaBase) (L := D.Hs n)
      (CurvatureInterpolation.continuous_kappaInterp
        (t := PathMetricCircle.B t) hk0c hk1c)
      (CurvatureInterpolation.periodic_kappaInterp
        (t := PathMetricCircle.B t) hper0 hper1)
      (CurvatureInterpolation.integral_kappaInterp
        (t := PathMetricCircle.B t) hk0c hk1c htot0 htot1)
  convert hp (s + phase W t) using 1 <;>
    simp [front, period, ProfiledInterpolationFields.Y] <;> ring

theorem phase_hasDerivAt (W : Output D Q n A) (t : ℝ) :
    HasDerivAt (phase W) (phaseRate W t) t := by
  simpa [phase, phaseRate] using W.sourceCertificate.field_flow 0 t

theorem phase_contDiff (W : Output D Q n A) : ContDiff ℝ 1 (phase W) := by
  have hdiff : Differentiable ℝ (phase W) :=
    fun t ↦ (phase_hasDerivAt W t).differentiableAt
  have hphaseC : Continuous (phase W) := hdiff.continuous
  have hrateC : Continuous (phaseRate W) := by
    simpa [phaseRate, uncurry] using W.sourceCertificate.field_cont.comp
      (continuous_id.prodMk hphaseC)
  rw [contDiff_one_iff_deriv]
  refine ⟨hdiff, ?_⟩
  convert hrateC using 1
  funext t
  exact (phase_hasDerivAt W t).deriv

theorem front_contDiff (W : Output D Q n A) :
    ContDiff ℝ 1 (uncurry (front W)) := by
  have hg : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      (p.1, p.2 + phase W p.1)) := by
    exact contDiff_fst.prodMk
      (contDiff_snd.add ((phase_contDiff W).comp contDiff_fst))
  simpa [front, Function.comp_def, uncurry] using
    W.sourceCertificate.Y_C1.comp hg

theorem angle_contDiff (W : Output D Q n A) :
    ContDiff ℝ 1 (uncurry (angle W)) := by
  have hg : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      (p.1, p.2 + phase W p.1)) := by
    exact contDiff_fst.prodMk
      (contDiff_snd.add ((phase_contDiff W).comp contDiff_fst))
  simpa [angle, Function.comp_def, uncurry] using
    W.sourceCertificate.angle_C1.comp hg

end ConfiguredBaseInterpolationShiftedFront
