import Mathlib
import UnitTangentIterates.InterpolationNormalizedPeriodicAdapter
import UnitTangentIterates.InterpolationSmooth

/-!
# The explicit interpolation in the normalized spatial parameter

The raw interpolation has front arclength `s` and full period `2L`.  Composing
with `s = 2L u` gives its normalized spatial slices.  This module records the
smoothness, closing, positive perimeter, and curvature bounds before the
separate tangential gauge is applied.
-/

noncomputable section

open Function Set Real MeasureTheory

namespace ExplicitNormalizedInterpolation

open CurvatureInterpolation InterpolationSmooth

variable {k0 k1 : ℝ → ℝ} {theta0 L kmin kmax : ℝ}

/-- **Normalized qualitative data of the explicit interpolation.** -/
theorem normalized_interpCurve_data
    (hL : 0 < L)
    (hk0 : ContDiff ℝ (3 : ℕ) k0) (hk1 : ContDiff ℝ (3 : ℕ) k1)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (hint0 : (∫ s in (0 : ℝ)..L, k0 s) = Real.pi)
    (hint1 : (∫ s in (0 : ℝ)..L, k1 s) = Real.pi)
    (hk0low : ∀ s, kmin ≤ k0 s) (hk1low : ∀ s, kmin ≤ k1 s)
    (hk0high : ∀ s, k0 s ≤ kmax) (hk1high : ∀ s, k1 s ≤ kmax) :
    let X : ℝ → ℝ → ℂ := fun t u =>
      interpCurve (kappaInterp k0 k1 t) theta0 L (2 * L * u)
    ContDiff ℝ (3 : ℕ) (uncurry X) ∧
      (∀ t, Periodic (X t) 1) ∧
      0 < 2 * L ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s,
        kmin ≤ kappaInterp k0 k1 t s) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s,
        kappaInterp k0 k1 t s ≤ kmax) := by
  dsimp only
  have hraw : ContDiff ℝ (3 : ℕ)
      (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s) :=
    contDiff_three_uncurry_interpCurve (theta0 := theta0) (L := L) hk0 hk1
  have hscale : ContDiff ℝ (3 : ℕ)
      (fun p : ℝ × ℝ => (p.1, 2 * L * p.2)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hXC : ContDiff ℝ (3 : ℕ)
      (uncurry fun t u => interpCurve (kappaInterp k0 k1 t) theta0 L (2 * L * u)) := by
    simpa [uncurry] using hraw.comp hscale
  have hper : ∀ t, Periodic
      (fun u => interpCurve (kappaInterp k0 k1 t) theta0 L (2 * L * u)) 1 := by
    intro t u
    have h := interpCurve_periodic (θ₀ := theta0)
      (continuous_kappaInterp hk0.continuous hk1.continuous)
      (periodic_kappaInterp (t := t) hper0 hper1)
      (integral_kappaInterp (t := t) hk0.continuous hk1.continuous hint0 hint1)
      (2 * L * u)
    convert h using 1 <;> ring
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, kmin ≤ kappaInterp k0 k1 t s := by
    intro t ht s
    simp only [kappaInterp]
    have h0 := hk0low s
    have h1 := hk1low s
    nlinarith [ht.1, ht.2]
  have hhigh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, kappaInterp k0 k1 t s ≤ kmax := by
    intro t ht s
    simp only [kappaInterp]
    have h0 := hk0high s
    have h1 := hk1high s
    nlinarith [ht.1, ht.2]
  exact ⟨hXC, hper, by positivity, hlow, hhigh⟩

end ExplicitNormalizedInterpolation
