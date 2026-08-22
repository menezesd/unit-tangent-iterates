import Mathlib
import UnitTangentIterates.NormalPathC2Increment

/-!
# The geometric path pseudodistance dominates the marked metric

`PathMetric.pathDist` is the infimum of the costs of *all* normal paths joining
two marked curves.  `NormalPathC2Increment.dist_le_cost` bounds the marked
distance of the two ends of a normal path by its cost, but only for a path
whose slices are constant-speed closed curves with the tube bounds — the
predicate `IsConstantSpeedNormalPath P₀ P₁ κ̂`.  Restricting the infimum to
those paths gives a pseudodistance for which the comparison does pass to the
infimum:

* `geomPathDist P₀ P₁ κ̂ p q` — the infimum of the costs of the *geometric*
  normal paths from `p` to `q`;
* `pathDist_le_geomPathDist` — it dominates the path pseudodistance, the
  infimum being taken over a smaller set;
* `dist_le_c2Const_mul_geomPathDist` — and it dominates the metric of the space
  of marked curves, up to the constant `c2Const P₀ P₁ κ̂`;
* `tendsto_of_geomPathDist_tendsto_zero` — hence convergence in the geometric
  path pseudodistance implies convergence in the marked geometric topology.
-/

noncomputable section

open Set Filter Topology MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace GeomPathDist

variable {p q : Data}

/-- The set of costs of the normal paths from `p` to `q` whose slices are
constant-speed closed curves with the tube bounds `P₀ ≤ P ≤ P₁`, `|κ| ≤ κ̂`. -/
def geomCostSet (P0 P1 khat : ℝ) (p q : Data) : Set ℝ :=
  {x | ∃ Γ : NormalPath p q, IsConstantSpeedNormalPath P0 P1 khat Γ ∧ cost Γ = x}

theorem geomCostSet_subset (P0 P1 khat : ℝ) (p q : Data) :
    geomCostSet P0 P1 khat p q ⊆ costSet p q := by
  rintro x ⟨Γ, -, rfl⟩
  exact ⟨Γ, rfl⟩

theorem bddBelow_geomCostSet (P0 P1 khat : ℝ) (p q : Data) :
    BddBelow (geomCostSet P0 P1 khat p q) := by
  refine ⟨0, ?_⟩
  rintro x ⟨Γ, -, rfl⟩
  exact Γ.cost_nonneg

/-- **The geometric path pseudodistance**: the infimum of the costs of the
normal paths joining two marked curves whose slices are constant-speed closed
curves with the tube bounds. -/
def geomPathDist (P0 P1 khat : ℝ) (p q : Data) : ℝ := sInf (geomCostSet P0 P1 khat p q)

theorem geomPathDist_nonneg (P0 P1 khat : ℝ) (p q : Data) :
    0 ≤ geomPathDist P0 P1 khat p q := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨Γ, -, rfl⟩
  exact Γ.cost_nonneg

theorem geomPathDist_le_cost {P0 P1 khat : ℝ} (Γ : NormalPath p q)
    (hΓ : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    geomPathDist P0 P1 khat p q ≤ cost Γ :=
  csInf_le (bddBelow_geomCostSet P0 P1 khat p q) ⟨Γ, hΓ, rfl⟩

/-- Taking the infimum over fewer paths can only increase it. -/
theorem pathDist_le_geomPathDist {P0 P1 khat : ℝ}
    (hne : (geomCostSet P0 P1 khat p q).Nonempty) :
    pathDist p q ≤ geomPathDist P0 P1 khat p q :=
  csInf_le_csInf (bddBelow_costSet p q) hne (geomCostSet_subset P0 P1 khat p q)

/-- **The geometric path pseudodistance dominates the metric of the space of
marked curves**, up to the constant of the increment bound. -/
theorem dist_le_c2Const_mul_geomPathDist {c kmin dlt cq kminq dltq P0 P1 khat : ℝ}
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hne : (geomCostSet P0 P1 khat p q).Nonempty) :
    dist p q ≤ c2Const P0 P1 khat * geomPathDist P0 P1 khat p q := by
  have hc2 : (0:ℝ) < c2Const P0 P1 khat := lt_of_lt_of_le one_pos (one_le_c2Const P0 P1 khat)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / c2Const P0 P1 khat := div_pos hε hc2
  obtain ⟨x, ⟨Γ, hΓ, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne
    (show geomPathDist P0 P1 khat p q
        < geomPathDist P0 P1 khat p q + ε / c2Const P0 P1 khat by linarith)
  have h1 : dist p q ≤ c2Const P0 P1 khat * cost Γ := dist_le_cost Γ hp hq hΓ
  have h2 : c2Const P0 P1 khat * cost Γ
      ≤ c2Const P0 P1 khat * (geomPathDist P0 P1 khat p q + ε / c2Const P0 P1 khat) :=
    mul_le_mul_of_nonneg_left hx.le hc2.le
  have h3 : c2Const P0 P1 khat * (geomPathDist P0 P1 khat p q + ε / c2Const P0 P1 khat)
      = c2Const P0 P1 khat * geomPathDist P0 P1 khat p q + ε := by
    field_simp
  linarith

/-- **Convergence in the geometric path pseudodistance implies convergence in
the marked geometric topology.** -/
theorem tendsto_of_geomPathDist_tendsto_zero {c kmin dlt cq kminq dltq P0 P1 khat : ℝ}
    {P : ℕ → Data} {q : Data}
    (hmem : ∀ n, IsTubeMember c kmin dlt (P n)) (hq : IsTubeMember cq kminq dltq q)
    (hne : ∀ n, (geomCostSet P0 P1 khat (P n) q).Nonempty)
    (h : Tendsto (fun n => geomPathDist P0 P1 khat (P n) q) atTop (𝓝 0)) :
    Tendsto P atTop (𝓝 q) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg)
    (fun n => dist_le_c2Const_mul_geomPathDist (hmem n) hq (hne n)) ?_
  simpa using h.const_mul (c2Const P0 P1 khat)

end GeomPathDist
