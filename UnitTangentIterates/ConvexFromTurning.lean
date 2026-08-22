import Mathlib

/-!
# One interval of increase and one of decrease

In the convexity step of the theorem *Regularizing backward shadowing* of the
paper *A Noncircular Oval with Convex Unit-Tangent Iterates* one reads:

> A regular closed plane curve with nonnegative curvature and turning number
> one bounds a convex body: in each direction, its scalar projection has one
> interval of increase and one of decrease, and therefore attains its maximum
> on a supporting line.

This file formalizes that mechanism.  A unit-speed curve `X` with tangent angle
`θ` has, in the direction `e^{iα}`, the scalar projection

```
  p(s) = Re( X(s) e^{-iα} ),      p'(s) = cos(θ(s) - α) .
```

If the tangent angle is nondecreasing (nonnegative curvature) and makes exactly
one turn, then `θ - α` runs monotonically from `-π/2` to `3π/2` over one
circuit, so `p` increases while `θ - α ≤ π/2` and decreases afterwards; the
maximum is attained at the parameter where `θ = α + π/2`, i.e. where the
tangent is orthogonal to `e^{iα}` — the supporting line in the direction
`e^{iα}`.

Main results:

* `hasDerivAt_projection` : `p'(s) = cos(θ(s) - α)`;
* `projection_monotoneOn`, `projection_antitoneOn` : the one interval of
  increase and the one interval of decrease;
* `projection_le_of_turning` : the projection attains its maximum at the
  supporting parameter.
-/

noncomputable section

open Real Set

namespace ConvexFromTurning

/-- The scalar projection of a unit-speed curve on the direction `e^{iα}` has
derivative `cos(θ - α)`. -/
theorem hasDerivAt_projection {X : ℝ → ℂ} {theta : ℝ → ℝ} {alpha s : ℝ}
    (hX : HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s) :
    HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      (Real.cos (theta s - alpha)) s := by
  have hmul : HasDerivAt (fun r => X r * Complex.exp (-(alpha : ℂ) * Complex.I))
      (Complex.exp ((theta s : ℂ) * Complex.I) * Complex.exp (-(alpha : ℂ) * Complex.I)) s :=
    hX.mul_const _
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hmul
  have hval : (Complex.exp ((theta s : ℂ) * Complex.I) *
      Complex.exp (-(alpha : ℂ) * Complex.I)).re = Real.cos (theta s - alpha) := by
    rw [← Complex.exp_add]
    have : ((theta s : ℂ) * Complex.I) + (-(alpha : ℂ) * Complex.I)
        = ((theta s - alpha : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have hre' : HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      ((Complex.exp ((theta s : ℂ) * Complex.I) *
        Complex.exp (-(alpha : ℂ) * Complex.I)).re) s := hre
  rwa [hval] at hre'

section Projection

variable {p theta : ℝ → ℝ} {alpha a b c : ℝ}

/-- **The interval of increase.**  While the tangent angle stays in
`[α - π/2, α + π/2]`, the projection increases. -/
theorem projection_monotoneOn
    (hp : ∀ s, HasDerivAt p (Real.cos (theta s - alpha)) s)
    (hrange : ∀ s ∈ Icc a c, theta s ∈ Icc (alpha - Real.pi / 2) (alpha + Real.pi / 2)) :
    MonotoneOn p (Icc a c) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact (Differentiable.continuous fun s => (hp s).differentiableAt).continuousOn
  · exact fun s _ => ((hp s).differentiableAt).differentiableWithinAt
  · intro s hs
    have hs' : s ∈ Icc a c := Ioo_subset_Icc_self (by simpa using hs)
    have hθ := hrange s hs'
    rw [(hp s).deriv]
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> [linarith [hθ.1]; linarith [hθ.2]]

/-- **The interval of decrease.**  Once the tangent angle has passed
`α + π/2`, and until it reaches `α + 3π/2`, the projection decreases. -/
theorem projection_antitoneOn
    (hp : ∀ s, HasDerivAt p (Real.cos (theta s - alpha)) s)
    (hrange : ∀ s ∈ Icc c b, theta s ∈ Icc (alpha + Real.pi / 2) (alpha + 3 * Real.pi / 2)) :
    AntitoneOn p (Icc c b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact (Differentiable.continuous fun s => (hp s).differentiableAt).continuousOn
  · exact fun s _ => ((hp s).differentiableAt).differentiableWithinAt
  · intro s hs
    have hs' : s ∈ Icc c b := Ioo_subset_Icc_self (by simpa using hs)
    have hθ := hrange s hs'
    rw [(hp s).deriv]
    have h1 : 0 ≤ Real.cos (theta s - alpha - Real.pi) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> [linarith [hθ.1]; linarith [hθ.2]]
    rw [Real.cos_sub_pi] at h1
    linarith

/-- **The projection attains its maximum at the supporting parameter.**  If the
tangent angle increases monotonically from `α - π/2` to `α + 3π/2` over one
circuit `[a, b]` and equals `α + π/2` at `c`, then the projection is maximal at
`c`: the curve lies in the half-plane bounded by the supporting line at `X(c)`
with outer normal `e^{iα}`. -/
theorem projection_le_of_turning
    (hp : ∀ s, HasDerivAt p (Real.cos (theta s - alpha)) s)
    (hmono : MonotoneOn theta (Icc a b))
    (hac : a ≤ c) (hcb : c ≤ b)
    (ha : alpha - Real.pi / 2 ≤ theta a) (hb : theta b ≤ alpha + 3 * Real.pi / 2)
    (hc : theta c = alpha + Real.pi / 2) :
    ∀ s ∈ Icc a b, p s ≤ p c := by
  have hinc : MonotoneOn p (Icc a c) := by
    apply projection_monotoneOn hp
    intro s hs
    have hsab : s ∈ Icc a b := ⟨hs.1, le_trans hs.2 hcb⟩
    have h1 : theta a ≤ theta s := hmono ⟨le_rfl, le_trans hac hcb⟩ hsab hs.1
    have h2 : theta s ≤ theta c := hmono hsab ⟨hac, hcb⟩ hs.2
    rw [hc] at h2
    exact ⟨by linarith, h2⟩
  have hdec : AntitoneOn p (Icc c b) := by
    apply projection_antitoneOn hp
    intro s hs
    have hsab : s ∈ Icc a b := ⟨le_trans hac hs.1, hs.2⟩
    have h1 : theta c ≤ theta s := hmono ⟨hac, hcb⟩ hsab hs.1
    have h2 : theta s ≤ theta b := hmono hsab ⟨le_trans hac hcb, le_rfl⟩ hs.2
    rw [hc] at h1
    exact ⟨h1, by linarith⟩
  intro s hs
  rcases le_total s c with h | h
  · exact hinc ⟨hs.1, h⟩ ⟨hac, le_rfl⟩ h
  · exact hdec ⟨le_rfl, hcb⟩ ⟨h, hs.2⟩ h

end Projection

end ConvexFromTurning
