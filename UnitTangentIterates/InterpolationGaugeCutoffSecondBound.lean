import Mathlib
import UnitTangentIterates.InterpolationGaugeFieldSecondState

/-! # Global second-state bound for the cutoff interpolation gauge -/

noncomputable section

open Set Function MeasureTheory

namespace InterpolationGauge

open CurvatureInterpolation InterpolationNormal InterpolationEstimate

variable {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd : ℝ}

/-- The fundamental-interval angle-shift estimate globalized by periodicity. -/
theorem abs_angleShift_le_global
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L) (s : ℝ) :
    |angleShift k0 k1 s| ≤ curvDist k0 k1 L := by
  obtain ⟨y, hy, hval⟩ :=
    (angleShift_periodic hk0 hk1 hper0 hper1 htot0 htot1).exists_mem_Ico₀ hL s
  rw [hval]
  exact abs_angleShift_le hk0 hk1 ⟨hy.1, hy.2.le⟩

/-- On the support of `timeCut`, the interpolated curvature is bounded by
`4*kstar`. -/
theorem abs_kappaInterp_le_on_cutoffSupport
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar)
    {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 2) (s : ℝ) :
    |kappaInterp k0 k1 t s| ≤ 4 * kstar := by
  have hks : 0 ≤ kstar := le_trans (hk0nn s) (hk0le s)
  have h1t : |1 - t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have htt : |t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  calc
    |kappaInterp k0 k1 t s| ≤ |1 - t| * |k0 s| + |t| * |k1 s| := by
      simpa [kappaInterp, abs_mul] using
        abs_add_le ((1 - t) * k0 s) (t * k1 s)
    _ ≤ 2 * kstar + 2 * kstar := by
      exact add_le_add
        (mul_le_mul h1t (by simpa [abs_of_nonneg (hk0nn s)] using hk0le s)
          (abs_nonneg _) (by norm_num))
        (mul_le_mul htt (by simpa [abs_of_nonneg (hk1nn s)] using hk1le s)
          (abs_nonneg _) (by norm_num))
    _ = 4 * kstar := by ring

/-- The spatial derivative of the interpolated curvature is bounded by
`4*kd` on the cutoff support. -/
theorem abs_kappaInterp_stateDeriv_le_on_cutoffSupport
    (hkd0 : ∀ s, |k0' s| ≤ kd) (hkd1 : ∀ s, |k1' s| ≤ kd)
    {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 2) (s : ℝ) :
    |(1 - t) * k0' s + t * k1' s| ≤ 4 * kd := by
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 s)
  have h1t : |1 - t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have htt : |t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  calc
    |(1 - t) * k0' s + t * k1' s| ≤ |1 - t| * |k0' s| + |t| * |k1' s| := by
      simpa [abs_mul] using abs_add_le ((1 - t) * k0' s) (t * k1' s)
    _ ≤ 2 * kd + 2 * kd := add_le_add
      (mul_le_mul h1t (hkd0 s) (abs_nonneg _) (by norm_num))
      (mul_le_mul htt (hkd1 s) (abs_nonneg _) (by norm_num))
    _ = 4 * kd := by ring

/-- Safe support bound for the first spatial derivative of the normal
velocity, using `eta_s = angleShift - kappa*xi`. -/
theorem abs_normalVelDeriv_le_on_cutoffSupport
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L)
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar)
    {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 2) (s : ℝ) :
    |normalVelDeriv k0 k1 theta0 L t s| ≤
      curvDist k0 k1 L + 4 * kstar * ((3 / 2) * L * curvDist k0 k1 L) := by
  rw [normalVelDeriv]
  calc
    |angleShift k0 k1 s - kappaInterp k0 k1 t s *
        tangentVel k0 k1 theta0 L t s| ≤
      |angleShift k0 k1 s| + |kappaInterp k0 k1 t s| *
        |tangentVel k0 k1 theta0 L t s| := by
          have h := abs_add_le (angleShift k0 k1 s)
            (-(kappaInterp k0 k1 t s * tangentVel k0 k1 theta0 L t s))
          simpa [abs_mul, sub_eq_add_neg] using h
    _ ≤ curvDist k0 k1 L + 4 * kstar * ((3 / 2) * L * curvDist k0 k1 L) :=
      add_le_add (abs_angleShift_le_global hk0 hk1 hper0 hper1 htot0 htot1 hL s)
        (mul_le_mul (abs_kappaInterp_le_on_cutoffSupport hk0nn hk1nn hk0le hk1le ht s)
          (abs_tangentVel_le (θ₀ := theta0) hk0 hk1 hper0 hper1 htot0 htot1 hL t s)
          (abs_nonneg _) (by linarith [hk0nn 0, hk0le 0]))

/-- Explicit global bound for the second state derivative of the cutoff gauge
field. -/
theorem abs_gaugeFieldStateSecond_le_global
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L)
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar)
    (hkd0 : ∀ s, |k0' s| ≤ kd) (hkd1 : ∀ s, |k1' s| ≤ kd)
    (t s : ℝ) :
    |gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s| ≤
      4 * kd * ((3 / 2) * L * curvDist k0 k1 L) +
        4 * kstar *
          (curvDist k0 k1 L + 4 * kstar * ((3 / 2) * L * curvDist k0 k1 L)) := by
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg (k0' 0)) (hkd0 0)
  have heps : 0 ≤ curvDist k0 k1 L :=
    integral_abs_sub_nonneg hk0 hk1 hL.le
  have hE : 0 ≤ (3 / 2) * L * curvDist k0 k1 L := by positivity
  have hE1 : 0 ≤ curvDist k0 k1 L +
      4 * kstar * ((3 / 2) * L * curvDist k0 k1 L) := by positivity
  have hRHS : 0 ≤ 4 * kd * ((3 / 2) * L * curvDist k0 k1 L) +
      4 * kstar * (curvDist k0 k1 L +
        4 * kstar * ((3 / 2) * L * curvDist k0 k1 L)) := by positivity
  rcases lt_or_ge t (-1) with htlow | htlow
  · rw [gaugeFieldStateSecond, timeCut_eq_zero_of_lt htlow]
    simp only [zero_mul, neg_zero, abs_zero]
    exact hRHS
  rcases lt_or_ge 2 t with hthigh | hthigh
  · rw [gaugeFieldStateSecond, timeCut_eq_zero_of_gt hthigh]
    simp only [zero_mul, neg_zero, abs_zero]
    exact hRHS
  have hsupp : -1 ≤ t ∧ t ≤ 2 := ⟨htlow, hthigh⟩
  have hcut : |timeCut t| ≤ 1 := by
    rw [abs_of_nonneg (timeCut_nonneg t)]
    exact timeCut_le_one t
  rw [gaugeFieldStateSecond, abs_neg, abs_mul]
  calc
    |timeCut t| * |_ * normalVel k0 k1 theta0 L t s +
        kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s| ≤
      1 * (4 * kd * ((3 / 2) * L * curvDist k0 k1 L) +
        4 * kstar * (curvDist k0 k1 L +
          4 * kstar * ((3 / 2) * L * curvDist k0 k1 L))) := by
      apply mul_le_mul hcut
      · calc
          |_ * normalVel k0 k1 theta0 L t s +
              kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s| ≤
            |(1 - t) * k0' s + t * k1' s| * |normalVel k0 k1 theta0 L t s| +
              |kappaInterp k0 k1 t s| * |normalVelDeriv k0 k1 theta0 L t s| := by
                simpa [abs_mul] using abs_add_le
                  (((1 - t) * k0' s + t * k1' s) * normalVel k0 k1 theta0 L t s)
                  (kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s)
          _ ≤ _ := add_le_add
            (mul_le_mul
              (abs_kappaInterp_stateDeriv_le_on_cutoffSupport hkd0 hkd1 hsupp s)
              (abs_normalVel_le (θ₀ := theta0) hk0 hk1 hper0 hper1 htot0 htot1 hL t s)
              (abs_nonneg _) (by linarith [hk0nn 0, hk0le 0]))
            (mul_le_mul
              (abs_kappaInterp_le_on_cutoffSupport hk0nn hk1nn hk0le hk1le hsupp s)
              (abs_normalVelDeriv_le_on_cutoffSupport hk0 hk1 hper0 hper1 htot0 htot1
                hL hk0nn hk1nn hk0le hk1le hsupp s)
              (abs_nonneg _) (by linarith [hk0nn 0, hk0le 0]))
      · exact abs_nonneg _
      · positivity
    _ = _ := one_mul _

end InterpolationGauge
