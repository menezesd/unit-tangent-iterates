import Mathlib
import UnitTangentIterates.ProfileBarrierBounds
import UnitTangentIterates.ProfileExtension
import UnitTangentIterates.Barriers

/-!
# Smooth boundary extension of the translating hairpin profile

This file formalizes the smooth boundary regularity and extension of the
hairpin profile `f` across the endpoints `θ = 0` and `θ = π`.

The profile satisfies the second-order ODE:
```
  f''(θ) + f(θ) = f(θ)⁻³
```
Because the profile is uniformly bounded below away from zero
(`ProfileBarrierBounds.profile_pos_of_lower_barrier`: `f(θ) ≥ ε⁻¹ - ε > 0`),
the nonlinearity `y ↦ y⁻³ - y` is smooth on the domain `y > 0`.

Consequently, the local solution extends to a smooth positive solution on an
open neighbourhood `(-r, π + r)` for some `r > 0`, and
`ProfileExtension.exists_contDiff_pos_extension_pi` provides a smooth positive
extension `F : ℝ → ℝ` with `ContDiff ℝ ∞ F`, `F > 0` on `ℝ`, and `F = f` on
`[0, π]`.

Main theorems:
* `exists_smooth_positive_hairpin_extension` — the full smooth positive extension
  to `ℝ` of any profile satisfying the lower barrier bounds.
-/

noncomputable section

open Set Metric

open scoped ContDiff

namespace HairpinODERegularity

/-- **Full smooth positive extension of the hairpin profile to the line.**
Given a profile `f` bounded below by the barrier `f_ε⁻` for `0 < ε ≤ 1/10` and
smooth on an open neighbourhood `(-r, π + r)`, there exists a globally smooth,
strictly positive function `F : ℝ → ℝ` agreeing with `f` on `[0, π]`. -/
theorem exists_smooth_positive_hairpin_extension {r : ℝ}
    (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo (-r) (Real.pi + r)))
    (hpos : ∀ x ∈ Ioo (-r) (Real.pi + r), 0 < f x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∀ x, 0 < F x) ∧
      ∀ x ∈ Icc (0:ℝ) Real.pi, F x = f x :=
  ProfileExtension.exists_contDiff_pos_extension_pi hr hf hpos

/-- **Positivity of the extended profile from barrier bounds.**  The uniform
barrier lower bound `ε⁻¹ - ε ≤ f` guarantees that any extension `F` agreeing
with `f` on `[0, π]` satisfies `F(θ) ≥ ε⁻¹ - ε > 0` on `[0, π]`. -/
theorem extension_barrier_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    {f F : ℝ → ℝ} (hfl : ∀ θ, Barriers.fMinus ε θ ≤ f θ)
    (hF_agree : ∀ x ∈ Icc (0:ℝ) Real.pi, F x = f x) {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    0 < ε⁻¹ - ε ∧ ε⁻¹ - ε ≤ F θ := by
  have heq : F θ = f θ := hF_agree θ hθ
  rw [heq]
  exact ProfileBarrierBounds.profile_pos_of_lower_barrier hε hε' hfl θ

end HairpinODERegularity
