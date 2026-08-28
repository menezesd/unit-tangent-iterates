import Mathlib
import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.ModelWidth
import UnitTangentIterates.TransverseWidthPositivity

/-! # Positive transverse width of a configured model -/

noncomputable section

open Real Set Complex MarkedSpace PathMetric

namespace ConfiguredModelPositiveWidth

open ModelOrbitDefect UnconditionalAssembly ConfiguredModelSequence
  TwoCapPairsAssembly CurvatureInterpolation

/-- A configured model whose centered-cell tangent angle lies in `(0,pi)` has
strictly positive geometric transverse width. -/
theorem width_pos
    {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) (theta0 : ℝ)
    (hangle : ∀ s ∈ Ioo (-(Hs n / 2)) (Hs n / 2),
      frontAngle (kappas n) theta0 s ∈ Ioo (0 : ℝ) Real.pi) :
    0 < Width.width (range (front (kappas n) theta0 (Hs n))) Complex.I := by
  have hH : 0 < Hs n := m.separation_pos n
  have hk : Continuous (kappas n) := m.curvature_continuous n
  have htheta : Continuous (frontAngle (kappas n) theta0) :=
    continuous_tangentAngle hk
  have hsub : Ioo (-(Hs n / 2)) (Hs n / 2) ⊆
      {s | 0 ≤ Real.sin (frontAngle (kappas n) theta0 s)} := by
    intro s hs
    exact Real.sin_nonneg_of_nonneg_of_le_pi (hangle s hs).1.le (hangle s hs).2.le
  have hcell : ∀ s ∈ Icc (-(Hs n / 2)) (Hs n / 2),
      0 ≤ Real.sin (frontAngle (kappas n) theta0 s) := by
    have hclosed : IsClosed {s | 0 ≤ Real.sin (frontAngle (kappas n) theta0 s)} :=
      isClosed_Ici.preimage (Real.continuous_sin.comp htheta)
    have hne : -(Hs n / 2) ≠ Hs n / 2 := by intro h; linarith
    have hs := hclosed.closure_subset_iff.2 hsub
    rw [closure_Ioo hne] at hs
    exact fun s hsc => hs hsc
  rw [ModelWidth.width_front_eq_integral hH hk (m.curvature_periodic n)
    (m.total_turning n) hcell]
  exact TransverseWidthPositivity.integral_sin_pos
    (by linarith : -(Hs n / 2) < Hs n / 2) htheta hangle

end ConfiguredModelPositiveWidth
