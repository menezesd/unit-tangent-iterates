import Mathlib
import UnitTangentIterates.GeomPathMetric
import UnitTangentIterates.GeomPathDistCircle

/-!
# Non-vacuity of the geometric pseudometric

The pseudometric statements of `GeomPathMetric.lean` are all conditional on the
existence of at least one geometric normal path joining the two curves.  This
file checks that the class is not empty, on the same family as
`GeomPathDistCircle.lean`: the dilations of the circles of radii `1 + 2^{-n}`
are geometric normal paths for the two-sided perimeter bounds
`P₀ = 2π ≤ 2πR(t) ≤ 4π = P₁` and `κ̂ = 1`, since the radii stay in `[1,2]`.

* `isGeomNormalPath_circlePath` — the dilation is a geometric normal path;
* `geomSet_circle_nonempty`, `geomDist_circle_le`,
  `tendsto_geomDist_circle` — the geometric cost set of two consecutive circles
  is nonempty and the pseudodistance tends to zero along the sequence;
* `dist_circle_le_geomDist` — the comparison with the marked metric;
* `geomDist_circle_triangle` — an instance of the triangle inequality;
* `isGeomCurve_circleData` and `geomDist_circle_self` — a circle of radius in
  `[1,2]` is a geometric curve, at geometric distance zero from itself.
-/

noncomputable section

open Set Filter Topology MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment GeomPathMetric SummableNormalPathLimitCircle

namespace GeomPathMetricCircle

/-- **The dilation of a circle is a geometric normal path**, for the two-sided
perimeter bounds `2π ≤ 2πR(t) ≤ 4π`: the slices are circles of arclength period
`2πR(t)`, tangent angle `2πu + π/2` and curvature `1/R(t)`. -/
theorem isGeomNormalPath_circlePath (n : ℕ) :
    IsGeomNormalPath (2 * Real.pi) (4 * Real.pi) 1 (circlePath n) := by
  have hpi := Real.pi_pos
  refine ⟨fun t => 2 * Real.pi * R n t, fun t => 2 * Real.pi * Rd n t,
    fun _ u => ang u, fun t _ => (R n t)⁻¹, fun _ _ => 0,
    fun t _ => -(Rd n t) / R n t ^ 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    nlinarith [R_ge n t]
  · intro t
    have := R_le n t
    nlinarith
  · intro t u
    rw [abs_of_nonneg (inv_nonneg.2 (R_pos n t).le)]
    rw [inv_le_one_iff₀]
    exact Or.inr (R_ge n t)
  · intro t u
    have h := ((hasDerivAt_normExp u).const_mul ((R n t : ℝ) : ℂ))
    have hfun : (circlePath n).X t = fun u : ℝ => ((R n t : ℝ) : ℂ) * normExp u := rfl
    rw [hfun]
    refine h.congr_deriv ?_
    rw [exp_ang]
    push_cast
    ring
  · intro t u
    have h : HasDerivAt (fun v : ℝ => 2 * Real.pi * v + Real.pi / 2) (2 * Real.pi) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 * Real.pi)).add_const (Real.pi / 2)
    refine h.congr_deriv ?_
    have hR := R_ne n t
    field_simp
  · exact fun t => ((hasDerivAt_R n t).const_mul (2 * Real.pi))
  · exact continuous_const.mul (continuous_Rd n)
  · intro t
    rw [circlePath_m, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    nlinarith [abs_nonneg (Rd n t)]
  · exact fun t u => hasDerivAt_const t (ang u)
  · exact fun u => continuous_const
  · intro t u
    rw [abs_zero, circlePath_m]
    positivity
  · intro t u
    exact (hasDerivAt_R n t).inv (R_ne n t)
  · exact fun u => ((continuous_Rd n).neg).div (continuous_id.pow 2 |>.comp
      (continuous_iff_continuousAt.2 fun t => (hasDerivAt_R n t).continuousAt))
      (fun t => pow_ne_zero 2 (R_ne n t))
  · intro t u
    rw [circlePath_m, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ R n t ^ 2)]
    have h1 : (1:ℝ) ≤ R n t ^ 2 := by nlinarith [R_ge n t]
    have h2 : |Rd n t| / R n t ^ 2 ≤ |Rd n t| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (Rd n t)]
    have h4 : (0:ℝ) ≤ 1 / (2 * Real.pi) ^ 2 * |Rd n t| := by positivity
    have h3 : |Rd n t| ≤ (1 / (2 * Real.pi) ^ 2 + 1 ^ 2) * |Rd n t| := by nlinarith [h4]
    linarith

/-- The geometric cost set of two consecutive circles of the sequence is
nonempty. -/
theorem geomSet_circle_nonempty (n : ℕ) :
    (geomSet (2 * Real.pi) (4 * Real.pi) 1
      (circleData (rad n)) (circleData (rad (n + 1)))).Nonempty :=
  ⟨cost (circlePath n), circlePath n, isGeomNormalPath_circlePath n, rfl⟩

/-- The geometric pseudodistance of two consecutive circles is at most the cost
of the dilation joining them, a geometric sequence. -/
theorem geomDist_circle_le (n : ℕ) :
    geomDist (2 * Real.pi) (4 * Real.pi) 1
        (circleData (rad n)) (circleData (rad (n + 1)))
      ≤ (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0:ℝ)..1, |wD t| := by
  have h := geomDist_le_cost (circlePath n) (isGeomNormalPath_circlePath n)
  rwa [cost_circlePath n] at h

/-- The geometric pseudodistance of two consecutive circles tends to zero. -/
theorem tendsto_geomDist_circle :
    Tendsto (fun n => geomDist (2 * Real.pi) (4 * Real.pi) 1
      (circleData (rad n)) (circleData (rad (n + 1)))) atTop (𝓝 0) := by
  have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0:ℝ)..1, |wD t|)
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
      simpa [pow_succ, mul_comm] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).mul_const (1 / 2 : ℝ)
    simpa using h.mul_const (∫ t in (0:ℝ)..1, |wD t|)
  exact squeeze_zero (fun n => geomDist_nonneg _ _ _ _ _) geomDist_circle_le hgeo

/-- **The comparison of the two metrics, on the sequence of circles.** -/
theorem dist_circle_le_geomDist (n : ℕ) :
    dist (circleData (rad n)) (circleData (rad (n + 1)))
      ≤ c2Const (2 * Real.pi) (4 * Real.pi) 1 *
        geomDist (2 * Real.pi) (4 * Real.pi) 1
          (circleData (rad n)) (circleData (rad (n + 1))) :=
  dist_le_c2Const_mul_geomDist (by positivity) (circleData_rad_mem n)
    (circleData_rad_mem (n + 1)) (geomSet_circle_nonempty n)

/-- **An instance of the triangle inequality**: two steps of the sequence of
circles. -/
theorem geomDist_circle_triangle (n : ℕ) :
    geomDist (2 * Real.pi) (4 * Real.pi) 1
        (circleData (rad n)) (circleData (rad (n + 2)))
      ≤ geomDist (2 * Real.pi) (4 * Real.pi) 1
          (circleData (rad n)) (circleData (rad (n + 1)))
        + geomDist (2 * Real.pi) (4 * Real.pi) 1
          (circleData (rad (n + 1))) (circleData (rad (n + 2))) := by
  have h := geomDist_triangle (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (khat := 1)
    (by positivity) (geomSet_circle_nonempty n) (geomSet_circle_nonempty (n + 1))
  simpa using h

/-- A circle of radius between `1` and `2` is a geometric curve. -/
theorem isGeomCurve_circleData {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    IsGeomCurve (2 * Real.pi) (4 * Real.pi) 1 (circleData r) := by
  have hpi := Real.pi_pos
  have hr : 0 < r := lt_of_lt_of_le one_pos h1
  refine ⟨2 * Real.pi * r, ang, fun _ => r⁻¹, by nlinarith, by nlinarith, ?_, ?_, ?_⟩
  · intro u
    rw [abs_of_nonneg (inv_nonneg.2 hr.le), inv_le_one_iff₀]
    exact Or.inr h1
  · intro u
    have h := ((hasDerivAt_normExp u).const_mul ((r : ℝ) : ℂ))
    have hfun : (⇑(circleData r).1) = fun u : ℝ => ((r : ℝ) : ℂ) * normExp u := rfl
    rw [hfun]
    refine h.congr_deriv ?_
    rw [exp_ang]
    push_cast
    ring
  · intro u
    have h : HasDerivAt (fun v : ℝ => 2 * Real.pi * v + Real.pi / 2) (2 * Real.pi) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 * Real.pi)).add_const (Real.pi / 2)
    refine h.congr_deriv ?_
    field_simp

/-- The circles of the sequence are at geometric distance zero from
themselves. -/
theorem geomDist_circle_self (n : ℕ) :
    geomDist (2 * Real.pi) (4 * Real.pi) 1 (circleData (rad n)) (circleData (rad n)) = 0 :=
  geomDist_self (isGeomCurve_circleData (rad_ge n) (rad_le n))

end GeomPathMetricCircle
