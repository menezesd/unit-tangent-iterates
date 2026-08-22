import Mathlib
import UnitTangentIterates.GeomPathDist
import UnitTangentIterates.SummableNormalPathLimitCircle

/-!
# Non-vacuity of the geometric path pseudodistance

The comparison `dist ≤ c2Const · geomPathDist` of `GeomPathDist.lean` is only
of use when the geometric cost set is nonempty.  The dilations of a circle of
`SummableNormalPathLimitCircle.lean` are geometric normal paths with `P₀ = 2π`,
`P₁ = 4π`, `κ̂ = 1`, so they witness that:

* `geomCostSet_circle_nonempty` — the geometric cost set of two consecutive
  circles of the sequence is nonempty;
* `geomPathDist_circle_le` — the geometric path pseudodistance of two
  consecutive circles is at most the cost of the dilation joining them;
* `tendsto_geomPathDist_circle` — it tends to zero along the sequence;
* `dist_circle_le_geomPathDist` — the comparison itself, on the sequence.
-/

noncomputable section

open Filter Topology MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment GeomPathDist SummableNormalPathLimitCircle

namespace GeomPathDistCircle

/-- The dilation joining two consecutive circles of the sequence is a geometric
normal path, so the geometric cost set is nonempty. -/
theorem geomCostSet_circle_nonempty (n : ℕ) :
    (geomCostSet (2 * Real.pi) (4 * Real.pi) 1
      (circleData (rad n)) (circleData (rad (n + 1)))).Nonempty :=
  ⟨cost (circlePath n), circlePath n, isConstantSpeedNormalPath_circlePath n, rfl⟩

/-- The geometric path pseudodistance of two consecutive circles is at most the
cost of the dilation joining them, a geometric sequence. -/
theorem geomPathDist_circle_le (n : ℕ) :
    geomPathDist (2 * Real.pi) (4 * Real.pi) 1
        (circleData (rad n)) (circleData (rad (n + 1)))
      ≤ (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0:ℝ)..1, |wD t| := by
  have h := geomPathDist_le_cost (circlePath n) (isConstantSpeedNormalPath_circlePath n)
  rwa [cost_circlePath n] at h

/-- The geometric path pseudodistance of two consecutive circles tends to
zero. -/
theorem tendsto_geomPathDist_circle :
    Tendsto (fun n => geomPathDist (2 * Real.pi) (4 * Real.pi) 1
      (circleData (rad n)) (circleData (rad (n + 1)))) atTop (𝓝 0) := by
  have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0:ℝ)..1, |wD t|)
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
      simpa [pow_succ, mul_comm] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)).mul_const (1 / 2 : ℝ)
    simpa using h.mul_const (∫ t in (0:ℝ)..1, |wD t|)
  exact squeeze_zero (fun n => geomPathDist_nonneg _ _ _ _ _) geomPathDist_circle_le hgeo

/-- **The comparison of the two metrics, on the sequence of circles.** -/
theorem dist_circle_le_geomPathDist (n : ℕ) :
    dist (circleData (rad n)) (circleData (rad (n + 1)))
      ≤ c2Const (2 * Real.pi) (4 * Real.pi) 1 *
        geomPathDist (2 * Real.pi) (4 * Real.pi) 1
          (circleData (rad n)) (circleData (rad (n + 1))) :=
  dist_le_c2Const_mul_geomPathDist (circleData_rad_mem n) (circleData_rad_mem (n + 1))
    (geomCostSet_circle_nonempty n)

end GeomPathDistCircle
