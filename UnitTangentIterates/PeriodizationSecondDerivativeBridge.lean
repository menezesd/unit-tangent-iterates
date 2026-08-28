import Mathlib
import UnitTangentIterates.PeriodizationDeriv
import UnitTangentIterates.PeriodizationSecondDerivative

/-! # The actual second period derivative of a periodization -/

noncomputable section

open Real Set Filter

namespace PeriodizationSecondDerivativeBridge

/-- The derivative of the periodization is itself differentiable, with the
termwise second-period-derivative series. -/
theorem hasDerivAt_deriv_periodization_period
    {z z1 z2 : ℝ → ℝ} {C alpha H0 H s : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0) (hH : H0 < H)
    (hz01 : ∀ x, HasDerivAt z (z1 x) x)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (deriv fun P => ∑' m : ℤ, z (s - (m : ℝ) * P))
      (∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H)) H := by
  let F : ℝ → ℝ := fun P => ∑' m : ℤ, z (s - (m : ℝ) * P)
  let G : ℝ → ℝ := fun P => ∑' m : ℤ, (-(m : ℝ)) * z1 (s - (m : ℝ) * P)
  have hG : HasDerivAt G
      (∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H)) H := by
    simpa [G] using
      PeriodizationSecondDerivative.hasDerivAt_firstPeriodDerivativeSeries
        halpha hH0 hH hz12 hz1b hz2b
  have heq : G =ᶠ[nhds H] deriv F := by
    filter_upwards [Ioi_mem_nhds hH] with P hP
    have hp := PeriodizationDeriv.hasDerivAt_periodization_period
      (z := z) (z' := z1) (C := C) (a := alpha) (H₀ := H0)
      (H := P) (s := s) halpha hH0 hz01 hzb hz1b hP
    simpa [F, G] using hp.deriv.symm
  have hout := hG.congr_of_eventuallyEq heq.symm
  simpa [F] using hout

/-- Paper-facing specialization at every positive period. -/
theorem hasDerivAt_deriv_periodization_period_of_pos
    {z z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz01 : ∀ x, HasDerivAt z (z1 x) x)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt
      (deriv fun P => ∑' m : ℤ, z (s - (m : ℝ) * P))
      (∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H)) H := by
  exact hasDerivAt_deriv_periodization_period
    halpha (by linarith : 0 < H / 2) (by linarith : H / 2 < H)
    hz01 hz12 hzb hz1b hz2b

/-- Explicit second-derivative value. -/
theorem second_deriv_periodization_period_of_pos
    {z z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz01 : ∀ x, HasDerivAt z (z1 x) x)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    deriv (deriv fun P => ∑' m : ℤ, z (s - (m : ℝ) * P)) H =
      ∑' m : ℤ, (m : ℝ) ^ 2 * z2 (s - (m : ℝ) * H) :=
  (hasDerivAt_deriv_periodization_period_of_pos
    halpha hH hz01 hz12 hzb hz1b hz2b).deriv

end PeriodizationSecondDerivativeBridge
