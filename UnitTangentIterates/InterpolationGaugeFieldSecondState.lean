import Mathlib
import UnitTangentIterates.InterpolationGauge
import UnitTangentIterates.InterpolationSecondOrder

/-! # Second state derivative of the interpolation gauge field -/

noncomputable section

open Set Function

namespace InterpolationGauge

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder

/-- The explicit second derivative in the state variable of `gaugeField`. -/
def gaugeFieldStateSecond (k0 k1 k0' k1' : ℝ → ℝ)
    (theta0 L t s : ℝ) : ℝ :=
  -(timeCut t *
    (((1 - t) * k0' s + t * k1' s) * normalVel k0 k1 theta0 L t s +
      kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s))

/-- Differentiate the already exported state derivative of the gauge field. -/
theorem hasDerivAt_gaugeField_stateDeriv
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hd0 : ∀ s, HasDerivAt k0 (k0' s) s)
    (hd1 : ∀ s, HasDerivAt k1 (k1' s) s) (t s : ℝ) :
    HasDerivAt
      (fun x => -(timeCut t *
        (kappaInterp k0 k1 t x * normalVel k0 k1 theta0 L t x)))
      (gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s) s := by
  have hk := hasDerivAt_kappaInterp (k0' := k0') (k1' := k1') hd0 hd1 t s
  have heta := hasDerivAt_normalVel (θ₀ := theta0) (L := L) hk0 hk1 t s
  have h := (hk.mul heta).const_mul (timeCut t)
  convert h.neg using 1

/-- Joint continuity of the second state derivative. -/
theorem continuous_uncurry_gaugeFieldStateSecond
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0' : Continuous k0') (hk1' : Continuous k1') :
    Continuous fun z : ℝ × ℝ =>
      gaugeFieldStateSecond k0 k1 k0' k1' theta0 L z.1 z.2 := by
  have hkp : Continuous fun z : ℝ × ℝ =>
      (1 - z.1) * k0' z.2 + z.1 * k1' z.2 :=
    ((continuous_const.sub continuous_fst).mul (hk0'.comp continuous_snd)).add
      (continuous_fst.mul (hk1'.comp continuous_snd))
  have hk := continuous_uncurry_kappaInterp (k0 := k0) (k1 := k1) hk0 hk1
  have heta := continuous_uncurry_normalVel (θ₀ := theta0) (L := L) hk0 hk1
  have heta1 := continuous_uncurry_normalVelDeriv
    (θ₀ := theta0) (L := L) hk0 hk1
  unfold gaugeFieldStateSecond
  exact ((continuous_timeCut.comp continuous_fst).mul
    ((hkp.mul heta).add (hk.mul heta1))).neg

/-- Uniform bound certificate on any chosen time region.  In applications the
four hypotheses are proved on the support `[-1,2]` of `timeCut`; no estimate
valid only on `[0,1]` is used outside its domain. -/
theorem abs_gaugeFieldStateSecond_le
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L Kp K E E1 : ℝ}
    (hKp : 0 ≤ Kp) (hK : 0 ≤ K) (hE : 0 ≤ E) (hE1 : 0 ≤ E1)
    (hkapPrime : ∀ t s,
      |(1 - t) * k0' s + t * k1' s| ≤ Kp)
    (hkap : ∀ t s, |kappaInterp k0 k1 t s| ≤ K)
    (heta : ∀ t s, |normalVel k0 k1 theta0 L t s| ≤ E)
    (heta1 : ∀ t s, |normalVelDeriv k0 k1 theta0 L t s| ≤ E1)
    (t s : ℝ) :
    |gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s| ≤
      Kp * E + K * E1 := by
  have hcut : |timeCut t| ≤ 1 := by
    rw [abs_of_nonneg (timeCut_nonneg t)]
    exact timeCut_le_one t
  rw [gaugeFieldStateSecond, abs_neg, abs_mul]
  calc
    |timeCut t| *
        |((1 - t) * k0' s + t * k1' s) * normalVel k0 k1 theta0 L t s +
          kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s|
        ≤ 1 * (Kp * E + K * E1) := by
          apply mul_le_mul hcut
          · calc
              |_ * normalVel k0 k1 theta0 L t s +
                  kappaInterp k0 k1 t s * normalVelDeriv k0 k1 theta0 L t s|
                  ≤ |(1 - t) * k0' s + t * k1' s| *
                      |normalVel k0 k1 theta0 L t s| +
                    |kappaInterp k0 k1 t s| *
                      |normalVelDeriv k0 k1 theta0 L t s| := by
                        simpa [abs_mul] using abs_add_le
                          (((1 - t) * k0' s + t * k1' s) *
                            normalVel k0 k1 theta0 L t s)
                          (kappaInterp k0 k1 t s *
                            normalVelDeriv k0 k1 theta0 L t s)
              _ ≤ Kp * E + K * E1 := by
                exact add_le_add
                  (mul_le_mul (hkapPrime t s) (heta t s) (abs_nonneg _) hKp)
                  (mul_le_mul (hkap t s) (heta1 t s) (abs_nonneg _) hK)
          · exact abs_nonneg _
          · positivity
    _ = Kp * E + K * E1 := one_mul _

end InterpolationGauge
