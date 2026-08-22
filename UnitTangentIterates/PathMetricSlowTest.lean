import Mathlib
import UnitTangentIterates.PathMetricSpeed
import UnitTangentIterates.MarkedShift

/-!
# Testing a bound on slow paths only

`PathMetric.pathDist_le_mul_of_maps_bounded_paths` turns an estimate valid for
the normal paths of duration one whose cost density is at most `(3/2)b` into a
Lipschitz bound for the marked geometric pseudodistance, but it is phrased for
a map of marked curves, the estimate producing a *path* between the images.

The estimates of this project are not of that shape: they bound a
pseudodistance — `PathMetric.pathDist` or `MarkedShift.pathDistShift` — of two
fixed marked curves by the cost of the path.  This file gives the version of
the criterion that fits them: for a fixed real number `D`,

```
  (∀ Γ, Γ.T = 1 → (∀ t, Γ.m t ≤ (3/2) b) → D ≤ C * cost Γ)  →  D ≤ C * pathDist p q ,
```

and its two specializations, on the normal speed
(`le_mul_pathDist_of_forall_slow_paths`) and to the pseudodistance taken modulo
the marking (`MarkedShift.pathDistShift_le_of_forall_slow_cost`).

The point is the same as in `PathMetricSpeed.lean`: by
`PathMetric.exists_unitTime_bounded_speed` a near-optimal path may always be
taken of duration one with its cost density at most `3/2` times its cost, so
nothing is lost by testing only the slow paths, while the constants of the
paper's estimates are then controlled by the pseudodistance alone.
-/

noncomputable section

open Set MarkedSpace

namespace PathMetric

open NormalPath

/-- **The cost density of a normal path is bounded.**  It is continuous and
vanishes outside the compact time interval of the path, so it attains a
maximum.  Consequently the hypothesis `∀ t, Γ.m t ≤ M` that the estimates with
the constant fixed by the speed of the path carry costs nothing: it holds for
every normal path, for a large enough `M`. -/
theorem NormalPath.exists_bound_m {p q : Data} (Γ : NormalPath p q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, Γ.m t ≤ M := by
  obtain ⟨t₀, -, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Γ.T)).exists_isMaxOn
      (Set.nonempty_Icc.mpr Γ.T_pos.le) Γ.cont_m.continuousOn
  refine ⟨Γ.m t₀, Γ.m_nonneg t₀, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0:ℝ) Γ.T
  · exact hmax ht
  · have : t ∉ Set.Ioo (0:ℝ) Γ.T := fun h => ht (Set.Ioo_subset_Icc_self h)
    rw [Γ.m_stop t this]
    exact Γ.m_nonneg t₀

/-- **A bound tested on slow paths.**  If the real number `D` is at most `C`
times the cost of every normal path of duration one from `p` to `q` whose cost
density is at most `(3/2)b`, and `b` exceeds the pseudodistance of `p` and `q`,
then `D ≤ C * pathDist p q`. -/
theorem le_mul_pathDist_of_forall_bounded_paths {p q : Data} {C b D : ℝ}
    (hC : 0 ≤ C) (hb : pathDist p q < b)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t, Γ.m t ≤ (3 / 2) * b) → D ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    D ≤ C * pathDist p q := by
  have hS : (costSet p q).Nonempty := ⟨cost hne.some, ⟨hne.some, rfl⟩⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  set d : ℝ := pathDist p q with hd_def
  set r : ℝ := min (ε / (C + 1)) (b - d) with hr_def
  have hrpos : 0 < r := lt_min (by positivity) (by linarith)
  -- a path of cost close to the pseudodistance
  obtain ⟨c, ⟨Γ, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hS
    (show d < d + r / 2 by linarith)
  -- run it at bounded speed
  obtain ⟨Δ, hT, hcost, hm⟩ := exists_unitTime_bounded_speed Γ (show (0:ℝ) < r / 2 by linarith)
  have hcostΔ : cost Δ ≤ d + r := by rw [hcost]; linarith
  have hmb : ∀ t, Δ.m t ≤ (3 / 2) * b := by
    intro t
    have h1 : cost Γ + r / 2 ≤ b := by
      have : r ≤ b - d := min_le_right _ _
      linarith
    have := hm t
    nlinarith
  have h1 : D ≤ C * cost Δ := h Δ hT hmb
  have h2 : C * cost Δ ≤ C * (d + r) := mul_le_mul_of_nonneg_left hcostΔ hC
  have h3 : C * r ≤ ε := by
    have hr : r ≤ ε / (C + 1) := min_le_left _ _
    have hCr : C * r ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hr hC
    have h4 : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hCpos]
      nlinarith
    linarith
  nlinarith

/-- **The same criterion phrased on the normal speed.**  The cost density of a
normal path dominates its normal speed, so it is enough to test the paths of
duration one along which the curve moves at speed at most `(3/2)b`. -/
theorem le_mul_pathDist_of_forall_slow_paths {p q : Data} {C b D : ℝ}
    (hC : 0 ≤ C) (hb : pathDist p q < b)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t u, |Γ.eta t u| ≤ (3 / 2) * b) →
      D ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    D ≤ C * pathDist p q :=
  le_mul_pathDist_of_forall_bounded_paths hC hb
    (fun Γ hT hm => h Γ hT (fun t u => le_trans (Γ.abs_eta_le t u) (hm t))) hne

end PathMetric

namespace MarkedShift

open PathMetric

/-- **The pseudodistance modulo the marking, bounded by testing slow paths
only.**  The analogue of `MarkedShift.pathDistShift_le_of_forall_cost` in which
the bound by the cost is required only along the normal paths of duration one
whose cost density is at most `(3/2)b`. -/
theorem pathDistShift_le_of_forall_bounded_cost {p q x y : Data} {K b : ℝ} (hK : 0 ≤ K)
    (hb : pathDist p q < b) (hne : Nonempty (NormalPath p q))
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t, Γ.m t ≤ (3 / 2) * b) →
      pathDistShift x y ≤ K * NormalPath.cost Γ) :
    pathDistShift x y ≤ K * pathDist p q :=
  PathMetric.le_mul_pathDist_of_forall_bounded_paths hK hb h hne

/-- **The same, phrased on the normal speed.** -/
theorem pathDistShift_le_of_forall_slow_cost {p q x y : Data} {K b : ℝ} (hK : 0 ≤ K)
    (hb : pathDist p q < b) (hne : Nonempty (NormalPath p q))
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t u, |Γ.eta t u| ≤ (3 / 2) * b) →
      pathDistShift x y ≤ K * NormalPath.cost Γ) :
    pathDistShift x y ≤ K * pathDist p q :=
  PathMetric.le_mul_pathDist_of_forall_slow_paths hK hb h hne

end MarkedShift
