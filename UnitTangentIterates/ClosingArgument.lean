import Mathlib
import UnitTangentIterates.Width

/-!
# The closing argument: a thin shadow is not a circle

This file formalizes, at the level of plane sets, the *Excluding a circle* step
that closes the proof of the main theorem of *A Noncircular Oval with Convex
Unit-Tangent Iterates*:

> By the lemma *Uniform transverse width*, the transverse width of the model
> `Q₀` is bounded uniformly, whereas its perimeter is `2H₀`.  The shadowing
> curve `X₀` is Hausdorff-close to `Q₀`, and a Hausdorff perturbation of size
> `d` changes every directional width by at most `2d`.  Therefore the width of
> `X₀` is at most `C_W + 2d`, whereas a circle of this perimeter would have
> width at least `(2H₀ − d)/π`; this is a contradiction.

The two geometric facts used here — the perturbation bound for widths and the
width of a disc — are in `UnitTangentIterates/Width.lean`.  What is added here is
the width of a *circle* (the sphere, i.e. the image of the closed curve rather
than the region it bounds), and the resulting criterion excluding a circle.

Main results:

* `Width.width_sphere` : the width of the circle of radius `r` is `2r`, in
  every direction;
* `width_sphere_of_perimeter` : a circle of perimeter `L = 2πr` has width
  `L/π`;
* `not_isCircle_of_width_lt` : a bounded set whose width in some direction is
  smaller than `L/π` is not a circle of perimeter `L`;
* `not_isCircle_of_hausdorffDist_le` : **the closing argument** — a set that is
  within Hausdorff distance `d` of a set of width at most `C_W`, and whose
  perimeter is at least `2H − d`, is not a circle, provided
  `C_W + 2d < (2H − d)/π`.
-/

noncomputable section

open Metric Set

namespace Width

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function of a sphere of radius `r ≥ 0` in a unit direction is
`⟪c, e⟫ + r`: the supremum is attained at the point `c + r • e` of the sphere. -/
theorem support_sphere {c : E} {r : ℝ} (hr : 0 ≤ r) {e : E} (he : ‖e‖ = 1) :
    support (sphere c r) e = (inner ℝ c e : ℝ) + r := by
  have hbdd : Bornology.IsBounded (sphere c r) :=
    (isBounded_closedBall (x := c) (r := r)).subset sphere_subset_closedBall
  have hmem : c + r • e ∈ sphere c r := by
    rw [mem_sphere, dist_eq_norm]
    simp [norm_smul, he, abs_of_nonneg hr]
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨c + r • e, hmem⟩)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x - c‖ = r := by
      rw [← dist_eq_norm]; exact mem_sphere.mp hx
    have hle : (inner ℝ (x - c) e : ℝ) ≤ ‖x - c‖ * ‖e‖ := real_inner_le_norm _ _
    rw [he, mul_one, hx'] at hle
    have hsplit : (inner ℝ x e : ℝ) = (inner ℝ c e : ℝ) + (inner ℝ (x - c) e : ℝ) := by
      rw [inner_sub_left]; ring
    show (inner ℝ x e : ℝ) ≤ (inner ℝ c e : ℝ) + r
    rw [hsplit]
    linarith
  · have hle := le_support hbdd (le_of_eq he) hmem
    have hval : (inner ℝ (c + r • e) e : ℝ) = (inner ℝ c e : ℝ) + r := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    rwa [hval] at hle

/-- **The width of the circle of radius `r` is `2r`**, in every direction. -/
theorem width_sphere {c : E} {r : ℝ} (hr : 0 ≤ r) {e : E} (he : ‖e‖ = 1) :
    width (sphere c r) e = 2 * r := by
  have hne : ‖-e‖ = 1 := by simpa using he
  rw [width, support_sphere hr he, support_sphere hr hne, inner_neg_right]
  ring

/-- A circle of perimeter `L = 2πr` has width `L/π` in every direction. -/
theorem width_sphere_of_perimeter {c : E} {r L : ℝ} (hr : 0 ≤ r) (hL : L = 2 * Real.pi * r)
    {e : E} (he : ‖e‖ = 1) : width (sphere c r) e = L / Real.pi := by
  rw [width_sphere hr he, hL]
  field_simp [Real.pi_ne_zero]

end Width

namespace ClosingArgument

open Width

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set is a *circle of perimeter `L`* if it is a metric sphere of positive
radius `r` with `L = 2πr`. -/
def IsCircleOfPerimeter (S : Set E) (L : ℝ) : Prop :=
  ∃ (c : E) (r : ℝ), 0 < r ∧ L = 2 * Real.pi * r ∧ S = sphere c r

/-- **A set that is too thin is not a circle**: if the width of `S` in some
unit direction is smaller than `L/π`, then `S` is not a circle of perimeter
`L`. -/
theorem not_isCircleOfPerimeter_of_width_lt {S : Set E} {L : ℝ} {e : E} (he : ‖e‖ = 1)
    (hw : width S e < L / Real.pi) : ¬ IsCircleOfPerimeter S L := by
  rintro ⟨c, r, hr, hL, rfl⟩
  rw [width_sphere_of_perimeter hr.le hL he] at hw
  exact lt_irrefl _ hw

/-- **The closing argument.**  Let `X` lie within Hausdorff distance `d` of a
model set `Q` whose width in the unit direction `e` is at most `C_W`, and let
`L ≥ 2H − d` be the perimeter of `X`.  If `C_W + 2d < (2H − d)/π`, then `X` is
not a circle of perimeter `L`. -/
theorem not_isCircleOfPerimeter_of_hausdorffDist_le {X Q : Set E}
    (hX : X.Nonempty) (hQ : Q.Nonempty)
    (hXb : Bornology.IsBounded X) (hQb : Bornology.IsBounded Q)
    {e : E} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hd : hausdorffDist X Q ≤ d) (hQw : width Q e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ¬ IsCircleOfPerimeter X L := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hwidth : width X e ≤ Cw + 2 * d := by
    have habs := abs_width_sub_le hX hQ hXb hQb (le_of_eq he) hd
    have := (abs_le.mp habs).2
    linarith
  refine not_isCircleOfPerimeter_of_width_lt he ?_
  have hmono : (2 * H - d) / Real.pi ≤ L / Real.pi := by
    gcongr
  linarith

end ClosingArgument
