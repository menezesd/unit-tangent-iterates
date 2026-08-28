import UnitTangentIterates.ConvexChordArc
import UnitTangentIterates.TwoCapPairsAssembly
import UnitTangentIterates.CurvatureInterpolation

/-!
# The near-diagonal chord bound for the model, without a curvature floor

§51 split the chord estimate into a near-diagonal part and a far part, and
showed only the far part needs a curvature floor.  This file discharges the near
part for the two-cap model front.

`chord_near_front` : for arclength separations below `2π/(3·kap)`, the chord is
at least half the separation.  The hypotheses are `0 ≤ κ ≤ kap` — the closed
convexity condition and the curvature ceiling — and nothing else.  In particular
the bound is uniform in the separation `H`.

What remains on this route is the far part: for separations above
`2π/(3·kap)`, the chord must be bounded below using the model's **width**
(§52 `WidthUniform.exists_uniform_width_lower`) rather than a curvature floor,
which needs the two-cap structure.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real


namespace TwoCapPairsAssembly

/-- **The near-diagonal chord bound for the model front, floor-free.**  Only
`0 ≤ κ ≤ kap` is used; no curvature floor appears.  For arclength separations
below `2π/(3·kap)` the chord is at least half the separation. -/
theorem chord_near_front {kappa : ℝ → ℝ} {theta0 H kap x y : ℝ}
    (hk : Continuous kappa) (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (hxy : x ≤ y) (hd : kap * (y - x) ≤ 2 * π / 3) :
    (y - x) / 2 ≤ ‖front kappa theta0 H y - front kappa theta0 H x‖ := by
  refine ConvexChordArc.chord_near (theta := frontAngle kappa theta0)
    (kappa := kappa) ?_ ?_ hk0 hkap hxy hd
  · intro s
    have h := front_hasDerivAt (kappa := kappa) (theta0 := theta0) (H := H) hk s
    have he : Complex.exp (Complex.I * (frontAngle kappa theta0 s : ℂ))
        = Complex.exp ((frontAngle kappa theta0 s : ℂ) * Complex.I) := by
      rw [mul_comm]
    rwa [he] at h
  · intro s
    exact CurvatureInterpolation.hasDerivAt_tangentAngle (θ₀ := theta0) hk s

end TwoCapPairsAssembly
