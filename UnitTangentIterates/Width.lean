import Mathlib

/-!
# Directional widths and Hausdorff perturbations

The closing argument of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates* excludes a circle by comparing widths: the shadowing curve `X₀` is
Hausdorff-close to the model `Q₀`, and

> a Hausdorff perturbation of size `d` changes every directional width by at
> most `2d`, whereas a circle with perimeter `L` has width `L/π`.

This file formalizes those two geometric facts in a real inner product space.
The directional width of a set `A` in the direction of a unit vector `e` is
written through the support function

```
  h_A(e) = sup { ⟪x, e⟫ : x ∈ A },      width_A(e) = h_A(e) + h_A(-e).
```

Main results:

* `support_le_of_hausdorffDist_le` : `h_A(e) ≤ h_B(e) + d` when
  `hausdorffDist A B ≤ d` and `‖e‖ ≤ 1`;
* `abs_width_sub_le` : a Hausdorff perturbation of size `d` changes every
  directional width by at most `2d`;
* `width_closedBall` : the width of a disc of radius `r` is `2r`, so a circle
  of perimeter `L = 2πr` has width `L/π`.
-/

noncomputable section

open Metric Set

namespace Width

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function `h_A(e) = sup {⟪x, e⟫ : x ∈ A}`. -/
def support (A : Set E) (e : E) : ℝ := sSup ((fun x => (inner ℝ x e : ℝ)) '' A)

/-- The width of `A` in the direction `e`. -/
def width (A : Set E) (e : E) : ℝ := support A e + support A (-e)

lemma bddAbove_image (A : Set E) (hA : Bornology.IsBounded A) {e : E} (he : ‖e‖ ≤ 1) :
    BddAbove ((fun x => (inner ℝ x e : ℝ)) '' A) := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).mp hA
  refine ⟨R, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  calc (inner ℝ x e : ℝ) ≤ ‖x‖ * ‖e‖ := real_inner_le_norm x e
    _ ≤ R * 1 := by
        apply mul_le_mul (hR x hx) he (norm_nonneg _)
        exact le_trans (norm_nonneg _) (hR x hx)
    _ = R := by ring

lemma le_support {A : Set E} (hA : Bornology.IsBounded A) {e : E} (he : ‖e‖ ≤ 1)
    {x : E} (hx : x ∈ A) : (inner ℝ x e : ℝ) ≤ support A e :=
  le_csSup (bddAbove_image A hA he) ⟨x, hx, rfl⟩

/-- **A Hausdorff perturbation moves the support function by at most `d`.** -/
theorem support_le_of_hausdorffDist_le {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B) {e : E} (he : ‖e‖ ≤ 1)
    {d : ℝ} (hd : hausdorffDist A B ≤ d) :
    support A e ≤ support B e + d := by
  have hfin : hausdorffEDist A B ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded hA hB hAb hBb
  apply csSup_le (hA.image _)
  rintro _ ⟨x, hx, rfl⟩
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  have hinf : infDist x B ≤ d := le_trans (infDist_le_hausdorffDist_of_mem hx hfin) hd
  have hlt : infDist x B < d + eps := by linarith
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hB).mp hlt
  have hsplit : (inner ℝ x e : ℝ) = (inner ℝ y e : ℝ) + (inner ℝ (x - y) e : ℝ) := by
    rw [inner_sub_left]
    ring
  have hcs : (inner ℝ (x - y) e : ℝ) ≤ ‖x - y‖ * ‖e‖ := real_inner_le_norm _ _
  have hnorm : ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
  have hbound : (inner ℝ (x - y) e : ℝ) ≤ d + eps := by
    calc (inner ℝ (x - y) e : ℝ) ≤ ‖x - y‖ * ‖e‖ := hcs
      _ ≤ ‖x - y‖ * 1 := by
          apply mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = dist x y := by rw [mul_one, hnorm]
      _ ≤ d + eps := hxy.le
  have hy' : (inner ℝ y e : ℝ) ≤ support B e := le_support hBb he hy
  show (inner ℝ x e : ℝ) ≤ support B e + d + eps
  rw [hsplit]
  linarith

/-- **A Hausdorff perturbation of size `d` changes every directional width by
at most `2d`.** -/
theorem abs_width_sub_le {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B) {e : E} (he : ‖e‖ ≤ 1)
    {d : ℝ} (hd : hausdorffDist A B ≤ d) :
    |width A e - width B e| ≤ 2 * d := by
  have hne : ‖-e‖ ≤ 1 := by simpa using he
  have hd' : hausdorffDist B A ≤ d := by rwa [hausdorffDist_comm]
  have h1 := support_le_of_hausdorffDist_le hA hB hAb hBb he hd
  have h2 := support_le_of_hausdorffDist_le hA hB hAb hBb hne hd
  have h3 := support_le_of_hausdorffDist_le hB hA hBb hAb he hd'
  have h4 := support_le_of_hausdorffDist_le hB hA hBb hAb hne hd'
  rw [abs_le]
  constructor <;> simp only [width] <;> linarith

/-! ### The width of a disc -/

/-- The support function of a closed ball of radius `r ≥ 0` in a unit direction
is `⟪c, e⟫ + r`. -/
theorem support_closedBall {c : E} {r : ℝ} (hr : 0 ≤ r) {e : E} (he : ‖e‖ = 1) :
    support (closedBall c r) e = (inner ℝ c e : ℝ) + r := by
  have hbdd : Bornology.IsBounded (closedBall c r) := isBounded_closedBall
  apply le_antisymm
  · apply csSup_le ((nonempty_closedBall.mpr hr).image _)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x - c‖ ≤ r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hx
    have : (inner ℝ (x - c) e : ℝ) ≤ ‖x - c‖ * ‖e‖ := real_inner_le_norm _ _
    rw [he, mul_one] at this
    have hsplit : (inner ℝ x e : ℝ) = (inner ℝ c e : ℝ) + (inner ℝ (x - c) e : ℝ) := by
      rw [inner_sub_left]; ring
    show (inner ℝ x e : ℝ) ≤ (inner ℝ c e : ℝ) + r
    rw [hsplit]
    linarith
  · have hmem : c + r • e ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm]
      simp [norm_smul, he, abs_of_nonneg hr]
    have := le_support hbdd (le_of_eq he) hmem
    have hval : (inner ℝ (c + r • e) e : ℝ) = (inner ℝ c e : ℝ) + r := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    rwa [hval] at this

/-- **The width of a disc of radius `r` is `2r`.**  Hence a circle of perimeter
`L = 2πr` has width `L/π`. -/
theorem width_closedBall {c : E} {r : ℝ} (hr : 0 ≤ r) {e : E} (he : ‖e‖ = 1) :
    width (closedBall c r) e = 2 * r := by
  have hne : ‖-e‖ = 1 := by simpa using he
  rw [width, support_closedBall hr he, support_closedBall hr hne, inner_neg_right]
  ring

/-- A circle of perimeter `L = 2πr` has width `L/π` in every direction. -/
theorem width_closedBall_of_perimeter {c : E} {r L : ℝ} (hr : 0 ≤ r)
    (hL : L = 2 * Real.pi * r) {e : E} (he : ‖e‖ = 1) :
    width (closedBall c r) e = L / Real.pi := by
  rw [width_closedBall hr he, hL]
  field_simp [Real.pi_ne_zero]

end Width
