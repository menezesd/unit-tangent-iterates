import UnitTangentIterates.CurvatureInterpolation

/-!
# Quantitative curvature pinch along the interpolation path

This file records the quantitative form of the curvature-preservation step in
Lemma `lem:curv-interp` of the paper.  The base interpolation file proves
strict positivity and preservation of a common upper ceiling.  For later
chord--arc and selected-rear estimates it is useful to retain a common positive
lower bound as well.
-/

namespace UnitTangentIterates

open Set CurvatureInterpolation

namespace CurvatureInterpolation

/-- Affine curvature interpolation preserves a common pointwise lower bound. -/
theorem kappaInterp_ge {k0 k1 : ℝ → ℝ} {kmin t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ s, kmin ≤ k0 s) (h1 : ∀ s, kmin ≤ k1 s) (s : ℝ) :
    kmin ≤ kappaInterp k0 k1 t s := by
  rw [kappaInterp]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (h0 s)),
    mul_nonneg ht.1 (sub_nonneg.mpr (h1 s))]

/-- The entire affine interpolation retains the common two-sided curvature
pinch of its endpoints.  This is the quantitative convexity clause used by
the chord--arc and selected-rear parts of the paper. -/
theorem kappaInterp_mem_Icc {k0 k1 : ℝ → ℝ} {kmin kmax t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ s, k0 s ∈ Icc kmin kmax)
    (h1 : ∀ s, k1 s ∈ Icc kmin kmax) (s : ℝ) :
    kappaInterp k0 k1 t s ∈ Icc kmin kmax := by
  constructor
  · exact kappaInterp_ge ht (fun x => (h0 x).1) (fun x => (h1 x).1) s
  · exact kappaInterp_le (fun x => (h0 x).2) (fun x => (h1 x).2) ht s

/-- In particular, interpolation between curvatures pinched in
`[kmin,kmax]`, with `kmin > 0`, stays uniformly strictly convex. -/
theorem kappaInterp_pos_of_pinched {k0 k1 : ℝ → ℝ} {kmin kmax t : ℝ}
    (hkmin : 0 < kmin) (ht : t ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ s, k0 s ∈ Icc kmin kmax)
    (h1 : ∀ s, k1 s ∈ Icc kmin kmax) (s : ℝ) :
    0 < kappaInterp k0 k1 t s :=
  lt_of_lt_of_le hkmin (kappaInterp_ge ht (fun x => (h0 x).1) (fun x => (h1 x).1) s)

end CurvatureInterpolation

end UnitTangentIterates
