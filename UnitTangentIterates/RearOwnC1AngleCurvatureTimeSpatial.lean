import UnitTangentIterates.RearOwnMixedOfInverseTimeSpatial

/-!
# Spatial derivative of the exact rear angle time field under C1 data

The tangential sliding created by the time-dependent inverse arclength is
handled through `hasDerivAt_slidingCoefficient`.  Thus no joint second
derivative of the inverse map is required.
-/

noncomputable section

open Function

namespace RearOwnC1AngleCurvatureTimeSpatial

open RearTrack RearOwnArclength RearOwnHigherRegularity
  RearOwnMixedOfInverseTimeSpatial

variable {ThetaT deltaT delta sf K KT : ℝ → ℝ → ℝ}

/-- The time derivative of the rear curvature `tan delta` in rear arclength. -/
def rearCurvatureTime (deltaT K delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦
    let s := sf t x
    (deltaT t s + partialTime sf t x *
      (K t s - Real.sin (delta t s))) / Real.cos (delta t s) ^ 2

/-- The exact C1 spatial compatibility between rear angle time and rear
curvature time. -/
theorem rearAngleTime_spatial
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hdeltaTTime : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hThetaTS : ∀ t s, HasDerivAt (ThetaT t) (KT t s) s)
    (hdeltaTS : ∀ t s, HasDerivAt (deltaT t)
      (-Real.cos (delta t s) * deltaT t s + KT t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsfS : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0) (t x : ℝ) :
    HasDerivAt (rearAngleTime ThetaT deltaT delta sf t)
      (rearCurvatureTime deltaT K delta sf t x) x := by
  let s := sf t x
  let d := delta t s
  let u := partialTime sf t x
  let c := Real.cos d
  let q : ℝ → ℝ := fun y ↦
    partialTime sf t y * Real.cos (delta t (sf t y))
  let k : ℝ → ℝ := fun y ↦ Real.tan (delta t (sf t y))
  have hTheta := (hThetaTS t s).comp x (hsfS t x)
  have hdeltaT := (hdeltaTS t s).comp x (hsfS t x)
  have hbase := hTheta.sub hdeltaT
  have hbase' : HasDerivAt
      (fun y ↦ ThetaT t (sf t y) - deltaT t (sf t y))
      (deltaT t s) x := by
    apply hbase.congr_deriv
    simp only [s, one_div]
    calc
      KT t (sf t x) * (Real.cos (delta t (sf t x)))⁻¹ -
          (-Real.cos (delta t (sf t x)) * deltaT t (sf t x) +
            KT t (sf t x)) * (Real.cos (delta t (sf t x)))⁻¹ =
          Real.cos (delta t (sf t x)) * deltaT t (sf t x) *
            (Real.cos (delta t (sf t x)))⁻¹ := by ring
      _ = deltaT t (sf t x) *
            (Real.cos (delta t (sf t x)) *
              (Real.cos (delta t (sf t x)))⁻¹) := by ring
      _ = deltaT t (sf t x) := by
        rw [mul_inv_cancel₀ (hcos t (sf t x)), mul_one]
  have hq : HasDerivAt q (deltaT t s * Real.tan d) x := by
    simpa only [q, s, d] using
      (hasDerivAt_slidingCoefficient hdeltaC hsfC
        hdeltaTTime
        hdeltaTC hsfS hinv hcos t x)
  have hd := (hsteer t s).comp x (hsfS t x)
  have htan0 : HasDerivAt Real.tan (1 / Real.cos d ^ 2) d :=
    Real.hasDerivAt_tan (hcos t s)
  have hk0 := htan0.comp x hd
  have hk : HasDerivAt k
      ((K t s - Real.sin d) / Real.cos d ^ 3) x := by
    simpa only [k, s, d, one_div] using hk0.congr_deriv (by
      field_simp [hcos t s]
      ring)
  have hsum := hbase'.add (hq.mul hk)
  have hfun : rearAngleTime ThetaT deltaT delta sf t =
      fun y ↦ ThetaT t (sf t y) - deltaT t (sf t y) + q y * k y := by
    funext y
    simp only [rearAngleTime, q, k]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos t (sf t y)]
  rw [hfun]
  apply hsum.congr_deriv
  have htrig := Real.sin_sq_add_cos_sq d
  change deltaT t s +
      (deltaT t s * Real.tan d * Real.tan d +
        (u * Real.cos d) *
          ((K t s - Real.sin d) / Real.cos d ^ 3)) =
    (deltaT t s + u * (K t s - Real.sin d)) / Real.cos d ^ 2
  rw [Real.tan_eq_sin_div_cos]
  have hc : Real.cos d ≠ 0 := hcos t s
  field_simp [hc]
  linear_combination (deltaT t s) * htrig

end RearOwnC1AngleCurvatureTimeSpatial
