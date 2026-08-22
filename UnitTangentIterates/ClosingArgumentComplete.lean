import Mathlib
import UnitTangentIterates.ClosingArgument
import UnitTangentIterates.WidthUniformProduced

/-!
# Complete closing contradiction argument and uniform width bounds

This file formalizes the unified statement of Proposition 7.2 (*Transverse Width
Contradiction Gap & Noncircularity*) from *A Noncircular Oval with Convex
Unit-Tangent Iterates*:

1. **Width of a Metric Sphere** (`Width.width_sphere_of_perimeter`):
   Any metric circle of perimeter `L = 2πr` has constant width:
   ```
     width(sphere(c, r), e) = L / π
   ```
   in every unit direction `‖e‖ = 1`.

2. **Closing Argument via Transverse Width Gap** (`ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le`):
   If `X` lies within Hausdorff distance `d` of a model curve `Q` with directional width
   `width(Q, e) ≤ C_W`, and its perimeter is `L ≥ 2H - d`, then whenever:
   ```
     C_W + 2d < (2H - d) / π
   ```
   `X` cannot be a metric circle of perimeter `L`.
-/

noncomputable section

open Metric Set Width ClosingArgument

namespace ClosingArgumentComplete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The complete closing contradiction theorem.** -/
theorem closing_argument_complete
    {X Q : Set E} (hX : X.Nonempty) (hQ : Q.Nonempty)
    (hXb : Bornology.IsBounded X) (hQb : Bornology.IsBounded Q)
    {e : E} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hd : hausdorffDist X Q ≤ d) (hQw : width Q e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    (∀ {c : E} {r : ℝ}, 0 ≤ r → L = 2 * Real.pi * r → width (sphere c r) e = L / Real.pi) ∧
    (¬ IsCircleOfPerimeter X L) := by
  refine ⟨fun {c r} hr hL => width_sphere_of_perimeter hr hL he,
    not_isCircleOfPerimeter_of_hausdorffDist_le hX hQ hXb hQb he hd hQw hL hgap⟩

end ClosingArgumentComplete
