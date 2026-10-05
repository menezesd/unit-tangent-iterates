module

public import Mathlib

/-!
# The width argument excluding a circle (end of Section 7)

The last step of the proof of Theorem 1.1 uses two facts:

* a set within distance `d` of a set lying in a strip of width `W` lies in a strip of width
  `W + 2d` (a Hausdorff perturbation of size `d` changes directional width by at most `2d`);
* a circle has perimeter `π` times its width in every direction.

Combining them: if a circle of radius `r` lies within distance `d` of a set contained in a
strip of width `W`, then `2r ≤ W + 2d`, so the perimeter `2πr` is at most `π (W + 2d)`.
Hence a closed curve of perimeter larger than `π (W + 2d)` that is `d`-close to a curve of
width `W` cannot be a circle.

Directions are unit complex numbers `v`, and the coordinate of `p` in direction `v` is
`Re(p · conj v)`.
-/

@[expose] public section

namespace Ovals

open Complex

/-- The coordinate in direction `v` changes by at most `‖v‖` times the distance. -/
lemma re_mul_conj_sub_le (z p v : ℂ) :
    (z * (starRingEnd ℂ) v).re - (p * (starRingEnd ℂ) v).re ≤ ‖z - p‖ * ‖v‖ := by
  rw [← Complex.sub_re, ← sub_mul]
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_conj]

/-- **Hausdorff perturbation of width.**  If every point of `T` is within distance `d` of the
set `S`, and `S` lies in the strip `α ≤ ⟨p, v⟩ ≤ α + W` (`‖v‖ = 1`), then `T` lies in the strip
`α - d ≤ ⟨z, v⟩ ≤ α + W + d`, of width `W + 2d`. -/
theorem strip_of_near {S T : Set ℂ} {v : ℂ} {d W α : ℝ} (hv : ‖v‖ = 1)
    (hS : ∀ p ∈ S, α ≤ (p * (starRingEnd ℂ) v).re ∧ (p * (starRingEnd ℂ) v).re ≤ α + W)
    (hT : ∀ z ∈ T, ∃ p ∈ S, ‖z - p‖ ≤ d) :
    ∀ z ∈ T, α - d ≤ (z * (starRingEnd ℂ) v).re ∧ (z * (starRingEnd ℂ) v).re ≤ α + W + d := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := hT z hz
  have h1 := re_mul_conj_sub_le z p v
  have h2 := re_mul_conj_sub_le p z v
  rw [hv, mul_one] at h1 h2
  rw [norm_sub_rev] at h2
  have := hS p hp
  constructor <;> linarith

/-- **A circle near a thin set is small.**  If every point of the circle `‖z - c‖ = r` is
within distance `d` of a set `S` lying in a strip of width `W`, then `2r ≤ W + 2d`. -/
theorem two_mul_radius_le {S : Set ℂ} {c v : ℂ} {r d W α : ℝ} (hv : ‖v‖ = 1) (hr : 0 ≤ r)
    (hS : ∀ p ∈ S, α ≤ (p * (starRingEnd ℂ) v).re ∧ (p * (starRingEnd ℂ) v).re ≤ α + W)
    (hd : ∀ z, ‖z - c‖ = r → ∃ p ∈ S, ‖z - p‖ ≤ d) : 2 * r ≤ W + 2 * d := by
  have hstrip := strip_of_near (T := {z | ‖z - c‖ = r}) hv hS (fun z hz => hd z hz)
  have hplus : ‖(c + r * v) - c‖ = r := by
    rw [add_sub_cancel_left, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
  have hminus : ‖(c - r * v) - c‖ = r := by
    rw [sub_sub_cancel_left, norm_neg, norm_mul, hv, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr]
  have h1 := (hstrip _ hplus).2
  have h2 := (hstrip _ hminus).1
  have hvv : (v * (starRingEnd ℂ) v).re = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; simp
  have e : ((c + r * v) * (starRingEnd ℂ) v).re - ((c - r * v) * (starRingEnd ℂ) v).re
      = 2 * r := by
    have : (c + r * v) * (starRingEnd ℂ) v - (c - r * v) * (starRingEnd ℂ) v
        = ((2 * r : ℝ) : ℂ) * (v * (starRingEnd ℂ) v) := by push_cast; ring
    rw [← Complex.sub_re, this, Complex.re_ofReal_mul, hvv, mul_one]
  linarith

/-- **Noncircularity criterion.**  A circle of radius `r` all of whose points are within
distance `d` of a set lying in a strip of width `W` has perimeter `2πr ≤ π (W + 2d)`.  So a
circle cannot have perimeter larger than `π (W + 2d)` under these hypotheses. -/
theorem circle_perimeter_le {S : Set ℂ} {c v : ℂ} {r d W α : ℝ} (hv : ‖v‖ = 1) (hr : 0 ≤ r)
    (hS : ∀ p ∈ S, α ≤ (p * (starRingEnd ℂ) v).re ∧ (p * (starRingEnd ℂ) v).re ≤ α + W)
    (hd : ∀ z, ‖z - c‖ = r → ∃ p ∈ S, ‖z - p‖ ≤ d) :
    2 * Real.pi * r ≤ Real.pi * (W + 2 * d) := by
  have := two_mul_radius_le hv hr hS hd
  nlinarith [Real.pi_pos]

end Ovals

end
