import Mathlib
import UnitTangentIterates.Width
import UnitTangentIterates.ClosingArgument
import UnitTangentIterates.UnitTangent

/-!
# Closing invariants under transported parametrizations

The paper's terminal orbit and noncircularity statements concern curve images,
not a preferred affine marking.  These adapters make that invariance explicit.
-/

noncomputable section

open Set Function

namespace RangeClosingAdapters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directional width is unchanged when two parametrized curves have the same
geometric image. -/
theorem width_range_eq_of_range_eq {X Y : ℝ → E} (hXY : range X = range Y)
    (e : E) : Width.width (range X) e = Width.width (range Y) e := by
  rw [hXY]

/-- Being a circle of a prescribed perimeter is a property of the image and
is therefore invariant under a transported periodic marking. -/
theorem isCircleOfPerimeter_range_iff {X Y : ℝ → E} (hXY : range X = range Y)
    (L : ℝ) :
    ClosingArgument.IsCircleOfPerimeter (range X) L ↔
      ClosingArgument.IsCircleOfPerimeter (range Y) L := by
  rw [hXY]

/-- Noncircularity transfers to every representative of the same geometric
curve, independently of its speed or marking. -/
theorem not_isCircleOfPerimeter_range_of_range_eq {X Y : ℝ → E}
    (hXY : range X = range Y) {L : ℝ}
    (hX : ¬ ClosingArgument.IsCircleOfPerimeter (range X) L) :
    ¬ ClosingArgument.IsCircleOfPerimeter (range Y) L := by
  rwa [← isCircleOfPerimeter_range_iff hXY L]

/-- Exact unit-tangent range orbits are stable under replacing either curve by
an arbitrary representative with the same image. -/
theorem unitTangent_range_orbit_of_representatives
    {X X' Y Y' : ℝ → ℂ}
    (hX : range X' = range X)
    (hY : range Y' = range Y)
    (horbit : range Y = range (UnitTangent.unitTangentMap X))
    (hT : range (UnitTangent.unitTangentMap X') =
      range (UnitTangent.unitTangentMap X)) :
    range Y' = range (UnitTangent.unitTangentMap X') := by
  rw [hY, horbit, hT]

end RangeClosingAdapters
