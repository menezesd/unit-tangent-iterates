import UnitTangentIterates.PathMetricSpeed
import UnitTangentIterates.PathMetricRescale

/-!
# A bounded-speed geometric schedule for countable normal tails

Suppose the `j`-th normal path has cost at most `C (q^2)^j`, with
`0 < q < 1`.  First use `exists_unitTime_bounded_speed` with extra cost
`C (q^2)^j`; then run the resulting path in time `q^j`.  The scheduled pieces
have

* duration `q^j`, hence summable total duration;
* cost at most `2 C (q^2)^j`;
* pointwise cost density at most `3 C q^j`, hence density tending to zero.

These are exactly the quantitative seam and accumulation-point hypotheses
missing from bare summability when constructing a countable concatenation.
-/

noncomputable section

open Filter Topology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace GeometricCountableNormalTailSchedule

variable {p : ℕ → MarkedSpace.Data}

/-- Unit-time bounded-speed representatives of a geometrically decaying path
chain. -/
structure SlowPieces
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (C q : ℝ) where
  q_pos : 0 < q
  q_lt_one : q < 1
  C_pos : 0 < C
  path : ∀ j, NormalPath (p j) (p (j + 1))
  time_one : ∀ j, (path j).T = 1
  cost_le : ∀ j, cost (path j) ≤ 2 * C * (q ^ 2) ^ j
  density_le : ∀ j t, (path j).m t ≤ 3 * C * (q ^ 2) ^ j

/-- Choose the slow representatives using the canonical bounded-speed
reparametrization. -/
theorem exists_slowPieces
    (step : ∀ j, NormalPath (p j) (p (j + 1)))
    {C q : ℝ} (hC : 0 < C) (hq0 : 0 < q) (hq1 : q < 1)
    (hcost : ∀ j, cost (step j) ≤ C * (q ^ 2) ^ j) :
    Nonempty (SlowPieces step C q) := by
  have heps : ∀ j : ℕ, 0 < C * (q ^ 2) ^ j := fun j => by positivity
  choose path htime hcostEq hdensity using fun j =>
    PathMetric.exists_unitTime_bounded_speed (step j) (heps j)
  refine ⟨{
    q_pos := hq0
    q_lt_one := hq1
    C_pos := hC
    path := path
    time_one := htime
    cost_le := fun j => ?_
    density_le := fun j t => ?_ }⟩
  · rw [hcostEq]
    nlinarith [hcost j]
  · exact (hdensity j t).trans (by nlinarith [hcost j])

namespace SlowPieces

variable {step : ∀ j, NormalPath (p j) (p (j + 1))} {C q : ℝ}

/-- Run the `j`-th slow representative in time `q^j`. -/
noncomputable def scheduled (S : SlowPieces step C q) (j : ℕ) :
    NormalPath (p j) (p (j + 1)) :=
  (S.path j).rescale (inv_pos.mpr (pow_pos S.q_pos j))

@[simp] theorem scheduled_time (S : SlowPieces step C q) (j : ℕ) :
    (S.scheduled j).T = q ^ j := by
  rw [scheduled, NormalPath.T_rescale, S.time_one]
  field_simp

theorem scheduled_cost_le (S : SlowPieces step C q) (j : ℕ) :
    cost (S.scheduled j) ≤ 2 * C * (q ^ 2) ^ j := by
  rw [scheduled, NormalPath.cost_rescale]
  exact S.cost_le j

theorem scheduled_density_le (S : SlowPieces step C q) (j : ℕ) (t : ℝ) :
    (S.scheduled j).m t ≤ 3 * C * q ^ j := by
  have hqj0 : 0 < q ^ j := pow_pos S.q_pos j
  have hmul := mul_le_mul_of_nonneg_left
    (S.density_le j ((q ^ j)⁻¹ * t)) (inv_nonneg.mpr hqj0.le)
  change (q ^ j)⁻¹ * (S.path j).m ((q ^ j)⁻¹ * t) ≤ 3 * C * q ^ j
  calc
    (q ^ j)⁻¹ * (S.path j).m ((q ^ j)⁻¹ * t)
        ≤ (q ^ j)⁻¹ * (3 * C * (q ^ 2) ^ j) := hmul
    _ = 3 * C * q ^ j := by
      rw [pow_two, mul_pow]
      field_simp

/-- The scheduled durations have finite total time. -/
theorem duration_summable (S : SlowPieces step C q) :
    Summable fun j : ℕ => (S.scheduled j).T := by
  simp only [S.scheduled_time]
  exact summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_pos S.q_pos]
    exact S.q_lt_one)

/-- The scheduled cost densities vanish uniformly at the accumulation
endpoint. -/
theorem density_bound_tendsto_zero (S : SlowPieces step C q) :
    Tendsto (fun j : ℕ => 3 * C * q ^ j) atTop (nhds 0) := by
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one S.q_pos.le S.q_lt_one).const_mul (3 * C)

/-- The scheduled costs remain summable. -/
theorem cost_summable (S : SlowPieces step C q) :
    Summable fun j : ℕ => cost (S.scheduled j) := by
  have hgeo : Summable fun j : ℕ => 2 * C * (q ^ 2) ^ j := by
    have hq2 : |q ^ 2| < 1 := by
      rw [abs_of_nonneg (sq_nonneg q)]
      nlinarith [S.q_pos, S.q_lt_one]
    exact (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using hq2)).mul_left
      (2 * C)
  exact hgeo.of_nonneg_of_le (fun j => (S.scheduled j).cost_nonneg)
    (S.scheduled_cost_le)

end SlowPieces

end GeometricCountableNormalTailSchedule
