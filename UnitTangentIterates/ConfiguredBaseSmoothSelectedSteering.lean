import UnitTangentIterates.ConstructedPulseWidthC3Shift
import UnitTangentIterates.ConfiguredActualSubunitCurvature
import UnitTangentIterates.ConfiguredApproximateDefectPathActualTerminal
import UnitTangentIterates.SelectedInverseSteeringSmooth
import UnitTangentIterates.PinchedPathSlow
import UnitTangentIterates.SecondOrderBounds

/-! # Smooth selected steering for the configured base interpolation

The original controlled junction uses the `C¹` time profile from
`PathMetricCircle`.  Recursive selected-rear regularity instead starts with
the flat smooth profile already used by the pinched-path construction.  This
module constructs the selected steering and inverse rear arclength before any
gauge marking is imposed.
-/

noncomputable section

open Function Set

namespace ConfiguredBaseSmoothSelectedSteering

open ConfiguredApproximateDefectPathActualTerminal

variable {D : ConstructedConfiguredSequenceWeighted.Data}

/-- A globally smooth interpolation parameter, constant near both ends. -/
def time (t : ℝ) : ℝ := PinchedPath.flatTime 1 t

/-- Its first derivative. -/
def speed (t : ℝ) : ℝ := PinchedPath.flatSpeed 1 t

/-- Its second derivative. -/
def accel (t : ℝ) : ℝ := deriv speed t

theorem time_mem_Icc (t : ℝ) : time t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa [time, PinchedPath.flatTime] using
      Real.smoothTransition.nonneg (2 * t - 1 / 2)
  · simpa [time, PinchedPath.flatTime] using
      Real.smoothTransition.le_one (2 * t - 1 / 2)

theorem contDiff_time (m : ℕ) : ContDiff ℝ m time := by
  simpa [time] using PinchedPath.contDiff_flatTime (n := m) 1

theorem contDiff_speed (m : ℕ) : ContDiff ℝ m speed := by
  simpa [speed] using PinchedPath.contDiff_flatSpeed (n := m) 1

theorem hasDerivAt_time (t : ℝ) : HasDerivAt time (speed t) t := by
  simpa [time, speed] using PinchedPath.hasDerivAt_flatTime 1 t

theorem hasDerivAt_speed (t : ℝ) : HasDerivAt speed (accel t) t := by
  exact ((contDiff_speed 1).differentiable (by norm_num) t).hasDerivAt

theorem continuous_speed : Continuous speed := (contDiff_speed 0).continuous

theorem continuous_accel : Continuous accel := by
  have h : ContDiff ℝ ((0 : ℕ) + 1) speed := by
    simpa using contDiff_speed 1
  exact (ContDiff.deriv' h).continuous

theorem speed_eq_zero_outside {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : speed t = 0 := by
  apply PinchedPath.flatSpeed_eq_zero_outside one_pos
  intro h
  exact ht ⟨h.1.le, h.2.le⟩

theorem accel_eq_zero_outside {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : accel t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · have heq : speed =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact PinchedPath.flatSpeed_of_lt one_pos (lt_trans hx (by norm_num))
    simpa [accel] using heq.deriv_eq
  · have heq : speed =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact PinchedPath.flatSpeed_of_gt one_pos (lt_trans (by norm_num) hx)
    simpa [accel] using heq.deriv_eq

/-- The smoothly profiled curvature and its exact time derivative. -/
def curvature (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  (1 - time t) * sourceK0 D n s + time t * sourceK1 D n s

def curvatureTime (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  speed t * (sourceK1 D n s - sourceK0 D n s)

def curvatureTime2 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  accel t * (sourceK1 D n s - sourceK0 D n s)

theorem sourceK0_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (sourceK0 D n) := by
  simpa [sourceK0] using C.model_KP_C3 n

theorem sourceK1_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (sourceK1 D n) := by
  simpa [sourceK1] using C.model_kH_C3 n

theorem curvature_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (uncurry (curvature D n)) := by
  have ht : ContDiff ℝ 3 (fun p : ℝ × ℝ => time p.1) :=
    (contDiff_time 3).comp contDiff_fst
  have h0 : ContDiff ℝ 3 (fun p : ℝ × ℝ => sourceK0 D n p.2) :=
    (sourceK0_C3 C n).comp contDiff_snd
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => sourceK1 D n p.2) :=
    (sourceK1_C3 C n).comp contDiff_snd
  simpa [curvature, uncurry, Function.comp_def] using
    ((contDiff_const.sub ht).mul h0).add (ht.mul h1)

theorem curvatureTime_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (uncurry (curvatureTime D n)) := by
  have hw : ContDiff ℝ 3 (fun p : ℝ × ℝ => speed p.1) :=
    (contDiff_speed 3).comp contDiff_fst
  have h0 : ContDiff ℝ 3 (fun p : ℝ × ℝ => sourceK0 D n p.2) :=
    (sourceK0_C3 C n).comp contDiff_snd
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => sourceK1 D n p.2) :=
    (sourceK1_C3 C n).comp contDiff_snd
  simpa [curvatureTime, uncurry, Function.comp_def] using hw.mul (h1.sub h0)

theorem curvature_time_deriv (n : ℕ) (t s : ℝ) :
    HasDerivAt (fun r => curvature D n r s) (curvatureTime D n t s) t := by
  convert (((hasDerivAt_const t 1).sub (hasDerivAt_time t)).mul_const
      (sourceK0 D n s)).add ((hasDerivAt_time t).mul_const (sourceK1 D n s)) using 1 <;>
    simp only [curvature, curvatureTime] <;> ring

theorem curvatureTime_time_deriv (n : ℕ) (t s : ℝ) :
    HasDerivAt (fun r => curvatureTime D n r s) (curvatureTime2 D n t s) t := by
  simpa [curvatureTime, curvatureTime2] using
    (hasDerivAt_speed t).mul_const (sourceK1 D n s - sourceK0 D n s)

/-- Smooth profiling supplies the global Lipschitz and quadratic Taylor
constants required by smooth dependence of the selected steering. -/
theorem exists_time_bounds
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    ∃ Klip CK : ℝ, 0 ≤ CK ∧
      (∀ a b s, |curvature D n a s - curvature D n b s| ≤ Klip * |a - b|) ∧
      (∀ a b s,
        |curvature D n a s - curvature D n b s -
          (a - b) * curvatureTime D n b s| ≤ CK * (a - b) ^ 2) := by
  obtain ⟨M1, hM10, hM1⟩ := SecondOrderBounds.exists_bound_of_vanishing_outside
    (a := (0 : ℝ)) (b := 1) continuous_speed
      (fun t ht => speed_eq_zero_outside (t := t) ht)
  obtain ⟨M2, hM20, hM2⟩ := SecondOrderBounds.exists_bound_of_vanishing_outside
    (a := (0 : ℝ)) (b := 1) continuous_accel
      (fun t ht => accel_eq_zero_outside (t := t) ht)
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hdiff : ∀ s, |sourceK1 D n s - sourceK0 D n s| ≤ H.k0 := by
    intro s
    rw [abs_le]
    constructor
    · have h0 := H.rear_nonnegative n s
      have h1 := H.front_le n s
      simpa [sourceK0, sourceK1, ← D.model.curvature_eq n] using
        (show -H.k0 ≤ (D.model.configs n).kH s - D.kappas n s by linarith)
    · have h0 := H.front_nonnegative n s
      have h1 := H.rear_le n s
      simpa [sourceK0, sourceK1, ← D.model.curvature_eq n] using
        (show (D.model.configs n).kH s - D.kappas n s ≤ H.k0 by linarith)
  refine ⟨M1 * H.k0, M2 * H.k0, mul_nonneg hM20 hk0, ?_, ?_⟩
  · intro a b s
    apply PathDataTaylorBounds.abs_sub_le_of_deriv_bound
      (fun t => curvature_time_deriv (D := D) n t s) _ a b
    intro t
    rw [curvatureTime, abs_mul]
    exact (mul_le_mul (hM1 t) (hdiff s) (abs_nonneg _) hM10).trans_eq (by ring)
  · intro a b s
    apply PathDataTaylorBounds.abs_taylor_le_of_deriv2_bound
      (fun t => curvature_time_deriv (D := D) n t s)
      (fun t => curvatureTime_time_deriv (D := D) n t s) _ a b
    intro t
    rw [curvatureTime2, abs_mul]
    exact (mul_le_mul (hM2 t) (hdiff s) (abs_nonneg _) hM20).trans_eq (by ring)

/-- Every configured edge with retained `C³` endpoint data has a jointly
`C⁴` selected steering and a differentiable inverse rear arclength for the
smoothly profiled interpolation. -/
theorem exists_selected
    (C : ConstructedPulseWidth.C3Certificate D)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Periodic (delta t) (2 * D.Hs n)) ∧
      (∀ t s, delta t s ∈ Icc (0 : ℝ) (Real.arcsin H.k0)) ∧
      (∀ t s, HasDerivAt (delta t)
        (curvature D n t s - Real.sin (delta t s)) s) ∧
      ContDiff ℝ 4 (uncurry delta) ∧
      ContDiff ℝ 4 (uncurry sf) ∧
      (∀ t x, RearTrack.rearArclength (delta t) (sf t x) = x) ∧
      (∀ t x, HasDerivAt (sf t)
        (1 / Real.cos (delta t (sf t x))) x) := by
  obtain ⟨Klip, CK, hCK, hLip, hTaylor⟩ := exists_time_bounds H n
  have hP : 0 < 2 * D.Hs n := mul_pos (by norm_num) (D.model.separation_pos n)
  have hper0 : Periodic (sourceK0 D n) (2 * D.Hs n) := by
    have h := (D.model.configs n).periodic_KP
    simpa [two_mul] using h.add_period h
  have hper1 : Periodic (sourceK1 D n) (2 * D.Hs n) := by
    have h := (D.model.configs n).periodic_kH
    simpa [sourceK1, two_mul] using h.add_period h
  have hKper : ∀ t, Periodic (curvature D n t) (2 * D.Hs n) := by
    intro t s
    simp only [curvature]
    rw [hper0 s, hper1 s]
  have hKdper : ∀ t, Periodic (curvatureTime D n t) (2 * D.Hs n) := by
    intro t s
    simp only [curvatureTime]
    rw [hper0 s, hper1 s]
  have hK0 : ∀ t s, 0 ≤ curvature D n t s := by
    intro t s
    have ht := time_mem_Icc t
    have h0 : 0 ≤ sourceK0 D n s := by
      simpa [sourceK0, ← D.model.curvature_eq n] using H.front_nonnegative n s
    have h1 : 0 ≤ sourceK1 D n s := by simpa [sourceK1] using H.rear_nonnegative n s
    dsimp [curvature]
    have ha := mul_nonneg (sub_nonneg.mpr ht.2) h0
    have hb := mul_nonneg ht.1 h1
    nlinarith
  have hKle : ∀ t s, curvature D n t s ≤ H.k0 := by
    intro t s
    have ht := time_mem_Icc t
    have h0 : sourceK0 D n s ≤ H.k0 := by
      simpa [sourceK0, ← D.model.curvature_eq n] using H.front_le n s
    have h1 : sourceK1 D n s ≤ H.k0 := by simpa [sourceK1] using H.rear_le n s
    dsimp [curvature]
    have ha := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0)
    have hb := mul_nonneg ht.1 (sub_nonneg.mpr h1)
    nlinarith
  obtain ⟨delta, sf, hper, hstrip, hsteer, -, -, hdelta4, hinv, hsfd⟩ :=
    SelectedInverseSteeringSmooth.exists_selected_steering_smooth
      hP (by
        exact (H.front_nonnegative n 0).trans (by
          simpa [sourceK0, ← D.model.curvature_eq n] using H.front_le n 0))
      H.k0_lt_one hKper hK0 hKle hKdper hLip hTaylor hCK
      (curvature_C3 C n) (curvatureTime_C3 C n)
  have hsf4 : ContDiff ℝ 4 (uncurry sf) := by
    exact RearOwnHigherRegularity.contDiff_sf (n := 3)
      (by
        exact (H.front_nonnegative n 0).trans (by
          simpa [sourceK0, ← D.model.curvature_eq n] using H.front_le n 0))
      H.k0_lt_one hdelta4
      (fun t s => (hstrip t s).1) (fun t s => (hstrip t s).2) hinv
  exact ⟨delta, sf, hper, hstrip, hsteer, hdelta4, hsf4, hinv, hsfd⟩

end ConfiguredBaseSmoothSelectedSteering
