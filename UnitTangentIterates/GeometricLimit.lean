import Mathlib

/-!
# Passing to the limit in marked geometric `C²` convergence

This file formalizes the last step of the lemma *Completeness of summable
normal paths* of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*: once the curves `X`, their unit tangents `τ`, their curvatures `κ`
and their speeds `g` converge uniformly in one transported periodic parameter,
one may pass to the limit in

```
  X_u = g τ,      τ_u = g κ ν
```

and conclude that the limit is a regular `C²` curve.

Curves are maps `ℝ → ℂ`, as elsewhere in the project; `ν = i τ`.

Main results:

* `hasDerivAt_of_uniform_limit` : the limit of curves whose derivatives
  converge uniformly is differentiable, with the limiting derivative;
* `norm_limit_eq_one` : the limiting tangent is again a unit vector;
* `le_norm_limit` : a uniform positive lower bound on the speeds passes to the
  limit, so the limit is regular;
* `limit_regular_C2` : the three statements combined.
-/

noncomputable section

open Filter Topology

namespace GeometricLimit

variable {Xn Vn : ℕ → ℝ → ℂ} {X V : ℝ → ℂ}

/-- **Differentiating a uniform limit.**  If `Xₙ' = Vₙ` everywhere, `Vₙ → V`
uniformly and `Xₙ → X` pointwise, then `X' = V`. -/
theorem hasDerivAt_of_uniform_limit
    (hderiv : ∀ n u, HasDerivAt (Xn n) (Vn n u) u)
    (hV : TendstoUniformly Vn V atTop)
    (hX : ∀ u, Tendsto (fun n => Xn n u) atTop (𝓝 (X u))) (u : ℝ) :
    HasDerivAt X (V u) u :=
  hasDerivAt_of_tendstoUniformly hV (Filter.Eventually.of_forall (fun n x => hderiv n x)) hX u

/-- The limit of unit vectors is a unit vector: the limiting tangent still has
length one. -/
theorem norm_limit_eq_one {Tn : ℕ → ℂ} {T : ℂ} (hone : ∀ n, ‖Tn n‖ = 1)
    (hT : Tendsto Tn atTop (𝓝 T)) : ‖T‖ = 1 := by
  have hnorm : Tendsto (fun n => ‖Tn n‖) atTop (𝓝 ‖T‖) := (continuous_norm.tendsto T).comp hT
  have hconst : Tendsto (fun n => ‖Tn n‖) atTop (𝓝 1) := by
    simp [hone]
  exact (tendsto_nhds_unique hconst hnorm).symm

/-- **The limiting speed is bounded away from zero**, so the limit curve is
regular. -/
theorem le_norm_limit {Wn : ℕ → ℂ} {W : ℂ} {c : ℝ} (hc : ∀ n, c ≤ ‖Wn n‖)
    (hW : Tendsto Wn atTop (𝓝 W)) : c ≤ ‖W‖ := by
  have hnorm : Tendsto (fun n => ‖Wn n‖) atTop (𝓝 ‖W‖) := (continuous_norm.tendsto W).comp hW
  exact ge_of_tendsto hnorm (Filter.Eventually.of_forall hc)

/-- **The limit of a marked geometric `C²`-convergent sequence is a regular
`C²` curve.**  The hypotheses are the uniform convergence of the curves, of
their velocities `Xₙ' = Vₙ` and of the velocity derivatives `Vₙ' = Aₙ`, together
with a uniform positive lower bound `c` on the speeds. -/
theorem limit_regular_C2 {An : ℕ → ℝ → ℂ} {Alim : ℝ → ℂ} {c : ℝ}
    (hderiv : ∀ n u, HasDerivAt (Xn n) (Vn n u) u)
    (hderiv2 : ∀ n u, HasDerivAt (Vn n) (An n u) u)
    (hVunif : TendstoUniformly Vn V atTop)
    (hAunif : TendstoUniformly An Alim atTop)
    (hXpt : ∀ u, Tendsto (fun n => Xn n u) atTop (𝓝 (X u)))
    (hspeed : ∀ n u, c ≤ ‖Vn n u‖) (u : ℝ) :
    HasDerivAt X (V u) u ∧ HasDerivAt V (Alim u) u ∧ c ≤ ‖V u‖ := by
  have hVpt : ∀ x, Tendsto (fun n => Vn n x) atTop (𝓝 (V x)) := fun x =>
    hVunif.tendsto_at x
  refine ⟨hasDerivAt_of_uniform_limit hderiv hVunif hXpt u, ?_, ?_⟩
  · exact hasDerivAt_of_uniform_limit hderiv2 hAunif hVpt u
  · exact le_norm_limit (fun n => hspeed n u) (hVpt u)

end GeometricLimit
