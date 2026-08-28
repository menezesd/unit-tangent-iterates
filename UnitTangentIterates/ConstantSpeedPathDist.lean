import UnitTangentIterates.ApproximateJacobiHypothesis
import UnitTangentIterates.GeomPathMetric

/-!
# The constant-speed path distance and its near-minimizers
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology MeasureTheory MarkedSpace PathMetric
  PathMetric.NormalPath
open NormalPathC2Increment

namespace PathMetric

/-- **The cost set of the constant-speed subclass.**  `costSet` records the
costs of *all* normal paths; this records the costs of those that are
constant-speed.  The distinction matters because `hmap` asks for a
constant-speed image path, and an infimum over the larger set carries no
information about the subclass. -/
def costSetCS (P0 P1 khat : ℝ) (p q : Data) : Set ℝ :=
  {c | ∃ Γ : NormalPath p q, IsConstantSpeedNormalPath P0 P1 khat Γ ∧ cost Γ = c}

theorem costSetCS_subset (P0 P1 khat : ℝ) (p q : Data) :
    costSetCS P0 P1 khat p q ⊆ costSet p q := by
  rintro c ⟨Γ, -, rfl⟩; exact ⟨Γ, rfl⟩

theorem bddBelow_costSetCS (P0 P1 khat : ℝ) (p q : Data) :
    BddBelow (costSetCS P0 P1 khat p q) := by
  refine ⟨0, ?_⟩; rintro c ⟨Γ, -, rfl⟩; exact Γ.cost_nonneg

/-- **The constant-speed path distance.** -/
def pathDistCS (P0 P1 khat : ℝ) (p q : Data) : ℝ := sInf (costSetCS P0 P1 khat p q)

theorem pathDist_le_pathDistCS {P0 P1 khat : ℝ} {p q : Data}
    (hne : (costSetCS P0 P1 khat p q).Nonempty) :
    pathDist p q ≤ pathDistCS P0 P1 khat p q :=
  csInf_le_csInf (bddBelow_costSet p q) hne (costSetCS_subset P0 P1 khat p q)

/-- **Near-minimizers exist inside the constant-speed subclass.**  This is the
statement §94 identified as the remaining obligation: not that the infimum is
attained, but that it can be approached *without leaving the subclass*.  It is
immediate once the infimum is taken over the subclass to begin with. -/
theorem exists_constantSpeed_near_minimizer {P0 P1 khat : ℝ} {p q : Data}
    (hne : ∃ Γ : NormalPath p q, IsConstantSpeedNormalPath P0 P1 khat Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : NormalPath p q, IsConstantSpeedNormalPath P0 P1 khat Γ ∧
      cost Γ ≤ pathDistCS P0 P1 khat p q + ε := by
  obtain ⟨Γ₀, hΓ₀⟩ := hne
  have hnonempty : (costSetCS P0 P1 khat p q).Nonempty := ⟨cost Γ₀, Γ₀, hΓ₀, rfl⟩
  obtain ⟨c, hc, hclt⟩ := Real.lt_sInf_add_pos hnonempty hε
  obtain ⟨Γ, hΓcs, rfl⟩ := hc
  exact ⟨Γ, hΓcs, le_of_lt hclt⟩

/-- **The approximate Jacobi hypothesis, from a bound on the constant-speed
distance.**  This is the exact interface `TubePullbackLimit.exists_path_iterate_approx`
consumes, and the exact form the Jacobi estimate delivers. -/
theorem hmap_approx_of_pathDistCS_le {B : Data → Data} {K P0 P1 khat : ℝ}
    (hne : ∀ p q : Data, ∃ Γ : NormalPath (B p) (B q),
      IsConstantSpeedNormalPath P0 P1 khat Γ)
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      IsConstantSpeedNormalPath P0 P1 khat Γ →
      pathDistCS P0 P1 khat (B p) (B q) ≤ K * cost Γ) :
    ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  intro p q Γ hΓ ε hε
  obtain ⟨Δ, hΔcs, hΔ⟩ := exists_constantSpeed_near_minimizer (hne p q) hε
  exact ⟨Δ, le_trans hΔ (by linarith [hbound p q Γ hΓ]), hΔcs⟩


/-- **The composed interface.**  A bound on the constant-speed path distance of
the image is enough to run the pullback iteration: no attainment, no extraction
of a minimizer, and the constant-speed property is carried because the infimum
was taken inside the subclass. -/
theorem exists_path_iterate_of_pathDistCS_le {B : Data → Data} {K P0 P1 khat : ℝ}
    (hK : 0 ≤ K)
    (hne : ∀ p q : Data, ∃ Γ : NormalPath (B p) (B q),
      IsConstantSpeedNormalPath P0 P1 khat Γ)
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      IsConstantSpeedNormalPath P0 P1 khat Γ →
      pathDistCS P0 P1 khat (B p) (B q) ≤ K * cost Γ)
    (k : ℕ) {p q : Data} (Γ : NormalPath p q)
    (hΓ : IsConstantSpeedNormalPath P0 P1 khat Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ : NormalPath (B^[k] p) (B^[k] q),
      cost Δ ≤ K ^ k * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ :=
  TubePullbackLimit.exists_path_iterate_approx hK
    (hmap_approx_of_pathDistCS_le hne hbound) k Γ hΓ ε hε


/-- **The entry point for every `pathDistCS` bound.**  A constant-speed path
witnesses its own cost as an upper bound for the constant-speed distance.  This
is how the two hypotheses of the pullback iteration are actually proved: exhibit
one constant-speed path and bound its cost, rather than reason about the
infimum. -/
theorem pathDistCS_le_cost {P0 P1 khat : ℝ} {p q : Data} (Γ : NormalPath p q)
    (h : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    pathDistCS P0 P1 khat p q ≤ cost Γ :=
  csInf_le (bddBelow_costSetCS P0 P1 khat p q) ⟨Γ, h, rfl⟩

/-- The same from the geometric class, which is where the repo's constant-speed
certificates are actually produced (`GeomPathMetric.IsGeomNormalPath.isConstantSpeed`). -/
theorem pathDistCS_le_cost_of_geom {P0 P1 khat : ℝ} {p q : Data} (hP0 : 0 ≤ P0)
    (Γ : NormalPath p q) (h : GeomPathMetric.IsGeomNormalPath P0 P1 khat Γ) :
    pathDistCS P0 P1 khat p q ≤ cost Γ :=
  pathDistCS_le_cost Γ (GeomPathMetric.IsGeomNormalPath.isConstantSpeed hP0 h)

end PathMetric
