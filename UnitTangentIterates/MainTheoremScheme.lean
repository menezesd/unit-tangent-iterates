import Mathlib
import UnitTangentIterates.ShadowingScheme
import UnitTangentIterates.MainTheoremConditional

/-!
# The main theorem from the shadowing scheme

`MainTheoremConditional.lean` states the closing step of the paper *A
Noncircular Oval with Convex Unit-Tangent Iterates* conditionally on the
**conclusion** of the shadowing theorem.  This file replaces that hypothesis by
the **hypotheses of the shadowing scheme** of `ShadowingScheme.lean`, which are
the estimates the rest of the project establishes:

* a complete metric space `M` of marked curves, with the parametrization map
  `ev : M → (ℝ → ℂ)` `1`-Lipschitz for the metric (the metric dominates the
  uniform distance of the parametrized curves);
* a selected inverse `B : M → M` which is non-expansive and continuous, and a
  forward map `T` with `T ∘ B = id` which is the unit-tangent transform on
  curves;
* every element of `M` is an oval, parametrized by arclength over its
  perimeter `Per`, and `Per` is Lipschitz for the metric;
* a model pseudo-orbit `Q` with summable defects, whose initial member has
  perimeter `2H` and transverse width at most `C_W`;
* the width gap `C_W + 2C_sh r₀ < (2H − C_sh r₀)/π` of the paper's
  large-separation lemma.

Under these hypotheses `main_theorem_of_scheme` produces an orbit of ovals
`𝒯Xₙ = X_{n+1}` whose initial member is **not** a circle.  The hypotheses are
still assumptions — the construction of the space `M` and of the pseudo-orbit
`Q` is not carried out here — but they are now the *inputs* of the shadowing
argument rather than its conclusion.
-/

noncomputable section

open Set Filter Topology Function

namespace MainTheoremScheme

/-- **The main theorem from the shadowing scheme.**  See the file header for a
description of the hypotheses.

NOTE (see `UnitTangentIterates/UnitTangentSpeed.lean`).  The orbit condition is
stated here as the identity of *parametrized* curves
`UnitTangent.unitTangentMap (X n) = X (n+1)`.  For a unit-speed curve of
curvature `k` the transform has speed `√(1 + k²) > 1`, so by
`UnitTangentSpeed.not_isOval_unitTangentMap` no oval has an oval as its
unit-tangent image: the combination of `IsOval (X n)` with that identity is
contradictory, and hypotheses of this shape can never be met.  The
geometrically correct statement asks only for equality of the images,
`range (X (n+1)) = range (UnitTangent.unitTangentMap (X n))`, i.e. equality up
to reparametrization; the corrected form of the closing argument is
`MarkedSpace.main_theorem_on_marked_space_range` in
`UnitTangentIterates/MarkedSchemeTheoremRange.lean`.
-/
theorem main_theorem_of_scheme {M : Type*} [MetricSpace M] [CompleteSpace M]
    {ev : M → ℝ → ℂ} {B T : M → M} {Per : M → ℝ} {Q : ℕ → M} {e : ℕ → ℝ}
    {Cw Csh Lp H : ℝ} {dir : ℂ}
    -- the scheme
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n)
    -- the space of curves
    (hev : ∀ m₁ m₂ t, dist (ev m₁ t) (ev m₂ t) ≤ dist m₁ m₂)
    (hevT : ∀ m, ev (T m) = UnitTangent.unitTangentMap (ev m))
    (hoval : ∀ m, MainTheoremConditional.IsOval (ev m))
    (hPerPos : ∀ m, 0 < Per m) (hPerPeriodic : ∀ m, Periodic (ev m) (Per m))
    (hPerLip : ∀ x y, |Per x - Per y| ≤ Lp * dist x y) (hLp : 0 ≤ Lp)
    -- the model
    (hCsh : 1 ≤ Csh) (hLpCsh : Lp ≤ Csh)
    (hPerQ : Per (Q 0) = 2 * H)
    (hdir : ‖dir‖ = 1)
    (hQw : Width.width (range (ev (Q 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * H - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, UnitTangent.unitTangentMap (X n) = X (n + 1)) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  -- the defects are nonnegative, hence the tails are
  have he : ∀ n, 0 ≤ e n := fun n => le_trans dist_nonneg (hdef n)
  have hr0 : 0 ≤ ShadowingTails.tail e 0 := ShadowingTails.tail_nonneg he 0
  -- the shadowing scheme produces the exact orbit
  obtain ⟨Z, -, horbT, hshadow, hLip, -⟩ :=
    ShadowingScheme.exists_shadowing_orbit_all (T := T) hB hBcont hT hsum hdef
  refine ⟨fun n => ev (Z n), Per (Z 0), fun n => hoval _, ?_, hPerPos _,
    hPerPeriodic _, ?_⟩
  · intro n
    rw [← hevT (Z n), horbT n]
  · -- the closing width argument
    set d : ℝ := Csh * ShadowingTails.tail e 0 with hd
    have hd0 : 0 ≤ d := mul_nonneg (le_trans zero_le_one hCsh) hr0
    have hdist : ∀ t, dist (ev (Z 0) t) (ev (Q 0) t) ≤ d := by
      intro t
      refine le_trans (hev (Z 0) (Q 0) t) (le_trans (hshadow 0) ?_)
      nlinarith
    have hper : 2 * H - d ≤ Per (Z 0) := by
      have h := hLip Per Lp hLp hPerLip 0
      rw [hPerQ] at h
      have h1 : Per (Z 0) - 2 * H ≥ -(Lp * ShadowingTails.tail e 0) := by
        cases' abs_le.mp h with h2 h3
        linarith
      have h2 : Lp * ShadowingTails.tail e 0 ≤ d := by
        rw [hd]
        exact mul_le_mul_of_nonneg_right hLpCsh hr0
      linarith
    exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H)
      (hoval (Z 0)).continuous (hPerPeriodic (Z 0)) (hPerPos (Z 0))
      (hoval (Q 0)).continuous (hPerPeriodic (Q 0)) (hPerPos (Q 0))
      hdir hd0 hdist hQw hper hgap

end MainTheoremScheme
