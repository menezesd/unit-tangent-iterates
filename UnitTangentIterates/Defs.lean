module

public import Mathlib

/-!
# Basic definitions: plane curves, the unit-tangent transform, ovals

We model the plane as `ℂ`.  A (parametrized) plane curve is a map `γ : ℝ → ℂ`.

* `Ovals.tau ψ` is the unit vector `(cos ψ, sin ψ)`.
* `Ovals.unitTangentTransform γ = γ + γ'/|γ'|` is the unit-tangent transform `𝒯`
  of the paper.  Since we divide by the speed, it does not depend on the
  (orientation preserving, regular) parametrization, so no arclength
  reparametrization is needed.
* `Ovals.curvature γ t` is the signed curvature `Im(conj γ' · γ'') / |γ'|³`
  (positive for counterclockwise convex curves).
* `Ovals.IsOval γ`: `γ` is a smooth regular closed simple curve with positive
  curvature everywhere, i.e. a smooth strictly convex closed curve traversed once
  counterclockwise.
* `Ovals.IsCircle γ`: the image of `γ` lies on a circle.
-/

@[expose] public section

namespace Ovals

open Complex Real
open scoped ContDiff

/-- The unit vector `τ(ψ) = (cos ψ, sin ψ)`, as a complex number. -/
noncomputable def tau (ψ : ℝ) : ℂ := Complex.exp ((ψ : ℂ) * Complex.I)

/-- The unit-tangent transform `𝒯γ = γ + τ_γ`, where `τ_γ = γ'/|γ'|` is the
positive unit tangent. -/
noncomputable def unitTangentTransform (γ : ℝ → ℂ) : ℝ → ℂ :=
  fun t => γ t + deriv γ t / ((‖deriv γ t‖ : ℝ) : ℂ)

/-- The signed curvature of a plane curve. -/
noncomputable def curvature (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ((starRingEnd ℂ) (deriv γ t) * deriv (deriv γ) t).im / ‖deriv γ t‖ ^ 3

/-- An *oval*: a smooth, regular, closed, simple plane curve with strictly positive
curvature (so it is the boundary of a strictly convex body, traversed once
counterclockwise). -/
structure IsOval (γ : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ γ
  regular : ∀ t, deriv γ t ≠ 0
  curvature_pos : ∀ t, 0 < curvature γ t
  closed_simple : ∃ p > 0, Function.Periodic γ p ∧ Set.InjOn γ (Set.Ico 0 p)

/-- The image of the curve lies on a circle. -/
def IsCircle (γ : ℝ → ℂ) : Prop := ∃ c : ℂ, ∃ r : ℝ, ∀ t, ‖γ t - c‖ = r

end Ovals

end
