import UnitTangentIterates.ConfiguredBaseSmoothSelectedSteering
import UnitTangentIterates.SelectedSteeringFamily
import UnitTangentIterates.SelectedSteeringChangeOfVariable
import UnitTangentIterates.ProfiledInterpolationGlobalBounds

/-! # Selected steering for the exact stopped configured interpolation -/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseProfiledSelectedSteeringC1

open ConfiguredApproximateDefectPathActualTerminal

variable {D : ConstructedConfiguredSequenceWeighted.Data}

def curvature (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  (1 - PathMetricCircle.B t) * sourceK0 D n s +
    PathMetricCircle.B t * sourceK1 D n s

def curvatureTime (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  PathMetricCircle.w t * (sourceK1 D n s - sourceK0 D n s)

theorem curvature_time_deriv (n : ℕ) (t s : ℝ) :
    HasDerivAt (fun r => curvature D n r s) (curvatureTime D n t s) t := by
  convert (((hasDerivAt_const t 1).sub (PathMetricCircle.hasDerivAt_B t)).mul_const
      (sourceK0 D n s)).add
      ((PathMetricCircle.hasDerivAt_B t).mul_const (sourceK1 D n s)) using 1 <;>
    simp only [curvature, curvatureTime] <;> ring

theorem source_diff_abs_le
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) (s : ℝ) :
    |sourceK1 D n s - sourceK0 D n s| ≤ H.k0 := by
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

theorem exists_time_bounds
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    ∃ Klip CK : ℝ, 0 ≤ CK ∧
      (∀ a b s, |curvature D n a s - curvature D n b s| ≤ Klip * |a - b|) ∧
      (∀ a b s,
        |curvature D n a s - curvature D n b s -
          (a - b) * curvatureTime D n b s| ≤ CK * (a - b) ^ 2) := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  refine ⟨3 / 2 * H.k0, 6 * H.k0, mul_nonneg (by norm_num) hk0, ?_, ?_⟩
  · intro a b s
    apply PathDataTaylorBounds.abs_sub_le_of_deriv_bound
      (fun t => curvature_time_deriv (D := D) n t s) _ a b
    intro t
    rw [curvatureTime, abs_mul, abs_of_nonneg (PathMetricCircle.w_nonneg t)]
    exact (mul_le_mul (PathMetricCircle.w_le_three_halves t)
      (source_diff_abs_le H n s) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  · intro a b s
    have hB := PathDataTaylorBounds.abs_taylor_le_of_lipschitz_deriv
      PathMetricCircle.hasDerivAt_B PathMetricCircle.lipschitzWith_w a b
    have heq : curvature D n a s - curvature D n b s -
        (a - b) * curvatureTime D n b s =
      (PathMetricCircle.B a - PathMetricCircle.B b -
        (a - b) * PathMetricCircle.w b) *
        (sourceK1 D n s - sourceK0 D n s) := by
      simp only [curvature, curvatureTime]
      ring
    rw [heq, abs_mul]
    calc
      |PathMetricCircle.B a - PathMetricCircle.B b -
          (a - b) * PathMetricCircle.w b| *
          |sourceK1 D n s - sourceK0 D n s|
          ≤ (6 : ℝ) * (a - b) ^ 2 * H.k0 :=
        mul_le_mul hB (source_diff_abs_le H n s) (abs_nonneg _) (by positivity)
      _ = (6 * H.k0) * (a - b) ^ 2 := by ring

theorem exists_selected
    (C : ConstructedPulseWidth.C3Certificate D)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Periodic (delta t) (2 * D.Hs n)) ∧
      (∀ t s, delta t s ∈ Icc (0 : ℝ) (Real.arcsin H.k0)) ∧
      (∀ t s, HasDerivAt (delta t)
        (curvature D n t s - Real.sin (delta t s)) s) ∧
      ContDiff ℝ 1 (uncurry delta) ∧
      ContDiff ℝ 1 (uncurry sf) ∧
      (∀ t x, rearArclength (delta t) (sf t x) = x) ∧
      (∀ t x, HasDerivAt (sf t)
        (1 / Real.cos (delta t (sf t x))) x) := by
  obtain ⟨Klip, CK, hCK, hLip, hTaylor⟩ := exists_time_bounds H n
  have hP : 0 < 2 * D.Hs n := mul_pos (by norm_num) (D.model.separation_pos n)
  have hper0 : Periodic (sourceK0 D n) (2 * D.Hs n) := by
    simpa [two_mul] using (D.model.configs n).periodic_KP.add_period
      (D.model.configs n).periodic_KP
  have hper1 : Periodic (sourceK1 D n) (2 * D.Hs n) := by
    simpa [sourceK1, two_mul] using (D.model.configs n).periodic_kH.add_period
      (D.model.configs n).periodic_kH
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
    have ht : PathMetricCircle.B t ∈ Icc (0 : ℝ) 1 :=
      ⟨PathMetricCircle.B_nonneg t, PathMetricCircle.B_le_one t⟩
    have h0 : 0 ≤ sourceK0 D n s := by
      simpa [sourceK0, ← D.model.curvature_eq n] using H.front_nonnegative n s
    have h1 : 0 ≤ sourceK1 D n s := by
      simpa [sourceK1] using H.rear_nonnegative n s
    dsimp [curvature]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2) h0)
      (mul_nonneg ht.1 h1)
  have hKle : ∀ t s, curvature D n t s ≤ H.k0 := by
    intro t s
    have ht : PathMetricCircle.B t ∈ Icc (0 : ℝ) 1 :=
      ⟨PathMetricCircle.B_nonneg t, PathMetricCircle.B_le_one t⟩
    have h0 : sourceK0 D n s ≤ H.k0 := by
      simpa [sourceK0, ← D.model.curvature_eq n] using H.front_le n s
    have h1 : sourceK1 D n s ≤ H.k0 := by
      simpa [sourceK1] using H.rear_le n s
    dsimp [curvature]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0),
      mul_nonneg ht.1 (sub_nonneg.mpr h1)]
  have hKcont : Continuous (uncurry (curvature D n)) := by
    have hB := PathMetricCircle.continuous_B.comp
      (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
    have h0 := (ConfiguredBaseSmoothSelectedSteering.sourceK0_C3 C n).continuous.comp
      (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
    have h1 := (ConfiguredBaseSmoothSelectedSteering.sourceK1_C3 C n).continuous.comp
      (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
    exact ((continuous_const.sub hB).mul h0).add (hB.mul h1)
  have hKdcont : Continuous (uncurry (curvatureTime D n)) := by
    have hw := PathMetricCircle.continuous_w.comp
      (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
    have h0 := (ConfiguredBaseSmoothSelectedSteering.sourceK0_C3 C n).continuous.comp
      (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
    have h1 := (ConfiguredBaseSmoothSelectedSteering.sourceK1_C3 C n).continuous.comp
      (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
    exact hw.mul (h1.sub h0)
  obtain ⟨delta, _, hper, hs0, hs1, hsteer, -, -⟩ :=
    SelectedSteeringFamily.exists_selected_steering_family
      (P := fun _ => 2 * D.Hs n) (K := curvature D n)
      (by exact (H.front_nonnegative n 0).trans (H.front_le n 0))
      H.k0_lt_one (fun _ => hP)
      (fun t => hKcont.comp (continuous_const.prodMk continuous_id))
      hKper hK0 hKle
  have hstrip : ∀ t s, delta t s ∈ Icc (0 : ℝ) (Real.arcsin H.k0) :=
    fun t s => ⟨hs0 t s, hs1 t s⟩
  obtain ⟨hdeltaC, sf, hinv, hsfC⟩ :=
    SelectedSteeringChangeOfVariable.exists_sf_of_curvature
      (K := curvature D n) (Kd := curvatureTime D n)
      hP (by exact (H.front_nonnegative n 0).trans (H.front_le n 0))
      H.k0_lt_one hKcont hKdcont hsteer hper hstrip hKdper hLip hTaylor hCK
  have hsfDeriv : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x := by
    intro t x
    have hroot : 0 < Real.sqrt (1 - H.k0 ^ 2) := Real.sqrt_pos.mpr (by
      nlinarith [H.k0_lt_one, (H.front_nonnegative n 0).trans (H.front_le n 0)])
    exact ArclengthInverse.hasDerivAt_of_rightInverse hroot
      (fun s => hasDerivAt_rearArclength
        (hdeltaC.continuous.comp (continuous_const.prodMk continuous_id)) s)
      (fun s => Shadowing.cos_ge_of_mem_strip (hstrip t s).1 (hstrip t s).2)
      (hinv t) x
  exact ⟨delta, sf, hper, hstrip, hsteer, hdeltaC, hsfC, hinv, hsfDeriv⟩

end ConfiguredBaseProfiledSelectedSteeringC1
