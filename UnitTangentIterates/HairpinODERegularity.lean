import Mathlib
import UnitTangentIterates.ProfileBarrierBounds
import UnitTangentIterates.ProfileExtension
import UnitTangentIterates.Barriers

/-!
# A staged smooth boundary extension interface

This file records the analytic interfaces needed to extend a hairpin profile
across the endpoints `θ = 0` and `θ = π`.

The profile satisfies the second-order ODE:
```
  f''(θ) + f(θ) = f(θ)⁻³
```
Because the profile is uniformly bounded below away from zero
(`ProfileBarrierBounds.profile_pos_of_lower_barrier`: `f(θ) ≥ ε⁻¹ - ε > 0`),
the nonlinearity `y ↦ y⁻³ - y` is smooth on the domain `y > 0`.

`ProfileODE.abs_second_le` proves the first quantitative implication of this
ODE: positive lower and upper barriers bound `f''`.  Once a smooth positive
continuation to an open neighbourhood `(-r, π + r)` has been established,
`ProfileExtension.exists_contDiff_pos_extension_pi` provides a smooth positive
extension `F : ℝ → ℝ` with `ContDiff ℝ ∞ F`, `F > 0` on `ℝ`, and `F = f` on
`[0, π]`.  The construction of that neighbourhood continuation from the
translator fixed-point equation is not asserted here.

Main theorems:
* `exists_smooth_positive_hairpin_extension` — the full smooth positive extension
  to `ℝ` of any profile satisfying the lower barrier bounds.
-/

noncomputable section

open Set Metric

open scoped ContDiff

namespace HairpinODERegularity

/-- The interior autonomous ODE satisfied by the translator profile, with
explicit first- and second-derivative witnesses.  This declaration was
previously referenced by the formalization manifest but had not actually been
defined. -/
structure ProfileODE (f fp fpp : ℝ → ℝ) (U : Set ℝ) : Prop where
  first_deriv : ∀ x ∈ U, HasDerivAt f (fp x) x
  second_deriv : ∀ x ∈ U, HasDerivAt fp (fpp x) x
  equation : ∀ x ∈ U, fpp x + f x = (f x)⁻¹ ^ 3

namespace ProfileODE

/-- Positive lower and upper barriers make the right side of
`f'' = f⁻³ - f` uniformly bounded.  This is the quantitative input for proving
that `f'` is uniformly Lipschitz up to the two endpoints. -/
theorem abs_second_le {f fp fpp : ℝ → ℝ} {U : Set ℝ} {m M : ℝ}
    (d : ProfileODE f fp fpp U) (hm : 0 < m)
    (hlower : ∀ x ∈ U, m ≤ f x) (hupper : ∀ x ∈ U, f x ≤ M) :
    ∀ x ∈ U, |fpp x| ≤ M + m⁻¹ ^ 3 := by
  intro x hx
  have hfxm := hlower x hx
  have hfxM := hupper x hx
  have hfx0 : 0 < f x := lt_of_lt_of_le hm hfxm
  have hM0 : 0 < M := lt_of_lt_of_le hfx0 hfxM
  have hinv : (f x)⁻¹ ≤ m⁻¹ := by
    exact (inv_le_inv₀ hfx0 hm).2 hfxm
  have hinv0 : 0 ≤ (f x)⁻¹ := inv_nonneg.mpr hfx0.le
  have him0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  have hcub : (f x)⁻¹ ^ 3 ≤ m⁻¹ ^ 3 := by
    exact pow_le_pow_left₀ hinv0 hinv 3
  have heq : fpp x = (f x)⁻¹ ^ 3 - f x := by
    linarith [d.equation x hx]
  rw [heq, abs_le]
  constructor
  · have : 0 ≤ (f x)⁻¹ ^ 3 := pow_nonneg hinv0 3
    nlinarith
  · nlinarith [pow_nonneg him0 3]

end ProfileODE

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
