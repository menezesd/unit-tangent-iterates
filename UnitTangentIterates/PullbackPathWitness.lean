import UnitTangentIterates.PathFromInfimum

/-!
# The scheme's `hmap` from the per-path Jacobi bound

The geometric path scheme asks for

```
  hmap : ∀ p q Γ, … → ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K · cost Γ ∧ … ,
```

a *witness* path of controlled cost.  What the Jacobi estimates give — and what
`SelInvPathLipschitz.pathDist_selInv_le_mul_pathDist` consumes — is a bound on
the *infimum*, `pathDist (B p) (B q) ≤ K · cost Γ`.

`exists_pullback_path_of_bound` converts one to the other by §63's extraction,
at the price of an additive margin.  `exists_pullback_path_relative` turns the
margin into an enlargement of the constant on paths of positive cost:
`cost Δ ≤ (K + δ)·cost Γ`.

That enlargement is harmless here precisely because §62 established that the
geometric variant does not need `K ≤ 1`: it needs `K·θ < 1` against
geometrically decaying defects, and `θ = e^{−β·Δ}` can absorb any fixed
enlargement of `K` by starting the orbit later.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace PathMetric

namespace PathMetric

open NormalPath

/-- **The `hmap` shape from the per-path Jacobi bound.**  The scheme asks for a
*witness* path of controlled cost; the Jacobi estimates give a bound on the
*infimum*.  §63's extraction converts one to the other, at the price of a
margin that can be made as small as one likes. -/
theorem exists_pullback_path_of_bound {B : Data → Data} {K : ℝ}
    (hne : ∀ p q : Data, Nonempty (NormalPath (B p) (B q)))
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      pathDist (B p) (B q) ≤ K * cost Γ)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ + eps := fun p q Γ =>
  exists_path_of_pathDist_le heps (hne p q) (hbound p q Γ)

/-- With a relative margin the constant is merely enlarged: on paths of positive
cost, `cost Δ ≤ (K + δ)·cost Γ`. -/
theorem exists_pullback_path_relative {B : Data → Data} {K delta : ℝ}
    (hne : ∀ p q : Data, Nonempty (NormalPath (B p) (B q)))
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      pathDist (B p) (B q) ≤ K * cost Γ)
    (hdelta : 0 < delta) :
    ∀ (p q : Data) (Γ : NormalPath p q), 0 < cost Γ →
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ (K + delta) * cost Γ := by
  intro p q Γ hpos
  obtain ⟨Δ, hΔ⟩ := exists_path_of_pathDist_le
    (show (0:ℝ) < delta * cost Γ by positivity) (hne p q) (hbound p q Γ)
  exact ⟨Δ, by nlinarith [hΔ]⟩

end PathMetric
