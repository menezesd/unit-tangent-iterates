import Mathlib
import UnitTangentIterates.CurvatureInterpolation

/-!
# A unit-speed curve is determined by its curvature up to a rigid motion

`CurvatureInterpolation.interpCurve κ θ₀ L` is the curve reconstructed from a
curvature function `κ`: it is unit speed, with tangent angle
`θ(s) = θ₀ + ∫₀ˢ κ`.  The statements of the project which compare *curves*
carrying two given curvatures — the matching estimate in the path
pseudodistance, `MatchingPathDist.pathDist_le_of_matching` — are stated for
that particular reconstruction.

This file supplies the classical rigidity that turns such a statement into one
about arbitrary curves: **a unit-speed curve with curvature `κ` is the image of
`interpCurve κ θ₀ L` under a rigid motion of the plane**, namely the rotation
by the difference of the two initial tangent angles followed by the translation
matching the two initial points.

* `tau_add` — the tangent direction is a character: `τ(a+b) = τ(a)τ(b)`;
* `tangentAngle_eq_of_hasDerivAt` — two tangent angles with the same derivative
  differ by the constant fixed at the origin;
* `eq_rigid_interpCurve` — the rigidity itself, in the form
  `X(s) = a + w · interpCurve κ θ₀ L (s)` with `‖w‖ = 1`;
* `exists_rigid_interpCurve` — its existential form;
* `exists_rigid_interpCurve_reparam` — the same for a curve given in an
  arbitrary parameter `u ↦ X(φ u)`, which is the shape in which the marked
  curves of `MarkedSpace.lean` carry a curvature.
-/

noncomputable section

open Real MeasureTheory CurvatureInterpolation

namespace CurvatureRigidity

/-- The unit tangent direction is a character of the additive group of angles. -/
theorem tau_add (a b : ℝ) : tau (a + b) = tau a * tau b := by
  simp only [tau, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **Two tangent angles with the same derivative differ by a constant.**  If
`θ' = κ` then `θ(s) = (θ(0) − θ₀) + (θ₀ + ∫₀ˢ κ)`. -/
theorem tangentAngle_eq_of_hasDerivAt {theta kappa : ℝ → ℝ} {θ₀ : ℝ}
    (hk : Continuous kappa) (hθ : ∀ s, HasDerivAt theta (kappa s) s) (s : ℝ) :
    theta s = (theta 0 - θ₀) + tangentAngle kappa θ₀ s := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y => theta y - tangentAngle kappa θ₀ y) 0 x := by
    intro x
    simpa using (hθ x).sub (hasDerivAt_tangentAngle (θ₀ := θ₀) hk x)
  have hdiff : Differentiable ℝ fun y => theta y - tangentAngle kappa θ₀ y :=
    fun x => (hd x).differentiableAt
  have hconst := is_const_of_deriv_eq_zero (f := fun y => theta y - tangentAngle kappa θ₀ y)
    hdiff (fun x => (hd x).deriv) s 0
  have h0 : tangentAngle kappa θ₀ 0 = θ₀ := tangentAngle_zero
  rw [h0] at hconst
  linarith [hconst]

/-- **A unit-speed curve with curvature `κ` is a rigid image of the
reconstruction `interpCurve κ θ₀ L`.**  The rotation is by the difference of the
initial tangent angles and the translation matches the initial points. -/
theorem eq_rigid_interpCurve {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {θ₀ L : ℝ}
    (hk : Continuous kappa) (hX : ∀ s, HasDerivAt X (tau (theta s)) s)
    (hθ : ∀ s, HasDerivAt theta (kappa s) s) (s : ℝ) :
    X s = (X 0 - tau (theta 0 - θ₀) * interpCurve kappa θ₀ L 0)
      + tau (theta 0 - θ₀) * interpCurve kappa θ₀ L s := by
  set w : ℂ := tau (theta 0 - θ₀) with hw
  have hd : ∀ x : ℝ, HasDerivAt (fun y => X y - w * interpCurve kappa θ₀ L y) 0 x := by
    intro x
    have h1 : HasDerivAt (fun y => w * interpCurve kappa θ₀ L y)
        (w * tau (tangentAngle kappa θ₀ x)) x :=
      (hasDerivAt_interpCurve (L := L) hk x).const_mul w
    have h2 : tau (theta x) = w * tau (tangentAngle kappa θ₀ x) := by
      rw [hw, ← tau_add]
      congr 1
      exact tangentAngle_eq_of_hasDerivAt (θ₀ := θ₀) hk hθ x
    have := (hX x).sub h1
    rwa [h2, sub_self] at this
  have hdiff : Differentiable ℝ fun y => X y - w * interpCurve kappa θ₀ L y :=
    fun x => (hd x).differentiableAt
  have hconst := is_const_of_deriv_eq_zero (f := fun y => X y - w * interpCurve kappa θ₀ L y)
    hdiff (fun x => (hd x).deriv) s 0
  have : X s - w * interpCurve kappa θ₀ L s = X 0 - w * interpCurve kappa θ₀ L 0 := hconst
  linear_combination (norm := ring_nf) this

/-- The existential form of the rigidity. -/
theorem exists_rigid_interpCurve {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} (θ₀ L : ℝ)
    (hk : Continuous kappa) (hX : ∀ s, HasDerivAt X (tau (theta s)) s)
    (hθ : ∀ s, HasDerivAt theta (kappa s) s) :
    ∃ a w : ℂ, ‖w‖ = 1 ∧ ∀ s, X s = a + w * interpCurve kappa θ₀ L s :=
  ⟨X 0 - tau (theta 0 - θ₀) * interpCurve kappa θ₀ L 0, tau (theta 0 - θ₀), norm_tau _,
    fun s => eq_rigid_interpCurve hk hX hθ s⟩

/-- **The rigidity for a curve given in an arbitrary parameter.**  A curve
`u ↦ X(φ u)` whose underlying unit-speed curve `X` has curvature `κ` is, in the
same parameter, a rigid image of the reconstruction. -/
theorem exists_rigid_interpCurve_reparam {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {phi : ℝ → ℝ}
    {Z : ℝ → ℂ} (θ₀ L : ℝ) (hk : Continuous kappa)
    (hX : ∀ s, HasDerivAt X (tau (theta s)) s) (hθ : ∀ s, HasDerivAt theta (kappa s) s)
    (hZ : ∀ u, Z u = X (phi u)) :
    ∃ a w : ℂ, ‖w‖ = 1 ∧ ∀ u, Z u = a + w * interpCurve kappa θ₀ L (phi u) := by
  obtain ⟨a, w, hw, h⟩ := exists_rigid_interpCurve θ₀ L hk hX hθ
  exact ⟨a, w, hw, fun u => by rw [hZ u, h (phi u)]⟩

end CurvatureRigidity
