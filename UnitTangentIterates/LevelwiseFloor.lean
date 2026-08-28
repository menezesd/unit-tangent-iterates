import UnitTangentIterates.FloorDecay

/-!
# The level-wise floor exists

§§47–48 established that no curvature floor is uniform in the level: the
constructed sequence has `kmins n ≤ π/Hₙ → 0`.  It is worth recording the
complementary fact, because the interpolation constructor depends on it.

`InterpolationEstimate.exists_interpolation_path` — the formal `lem:curv-interp`
— asks for `0 < k₀ r` and `0 < k₁ r` pointwise.  Those are *level-wise*
hypotheses, one pair of curves at a time, and they are available:

* `exists_levelwise_floor` — a continuous periodic positive curvature attains a
  positive minimum on one period, hence is bounded below by a positive constant;
* `exists_levelwise_pinch` — with the ceiling, the level's curvature is pinched.

So the two facts sit together without conflict: **at each level a positive floor
exists; no positive floor works for all levels at once.**  The closing theorem
asked for the second and had to be repaired (§§49–50); the interpolation
constructor asks only for the first and needs no repair.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function

namespace CurvatureFloorObstruction

/-- **The level-wise floor exists.**  A continuous periodic positive curvature
attains a positive minimum on one period, hence is bounded below by a positive
constant everywhere.  §48 showed no floor can be *uniform in the level*; this
records that at each level one does exist, which is what
`InterpolationEstimate.exists_interpolation_path` asks for. -/
theorem exists_levelwise_floor {k : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hk : Continuous k) (hper : Periodic k L) (hpos : ∀ s, 0 < k s) :
    ∃ c : ℝ, 0 < c ∧ ∀ s, c ≤ k s := by
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (s := Icc (0:ℝ) L) ⟨0, le_rfl, hL.le⟩ hk.continuousOn
  refine ⟨k t0, hpos t0, fun s => ?_⟩
  obtain ⟨t, ht, hst⟩ := hper.exists_mem_Ico₀ hL s
  rw [hst]
  exact hmin ⟨ht.1, ht.2.le⟩

/-- Consequently the interpolation hypotheses are satisfiable level by level:
a level's curvature is bounded between a positive floor and its ceiling. -/
theorem exists_levelwise_pinch {k : ℝ → ℝ} {L kap : ℝ} (hL : 0 < L)
    (hk : Continuous k) (hper : Periodic k L) (hpos : ∀ s, 0 < k s)
    (hle : ∀ s, k s ≤ kap) :
    ∃ c : ℝ, 0 < c ∧ (∀ s, c ≤ k s) ∧ ∀ s, k s ≤ kap := by
  obtain ⟨c, hc, hcle⟩ := exists_levelwise_floor hL hk hper hpos
  exact ⟨c, hc, hcle, hle⟩

end CurvatureFloorObstruction
