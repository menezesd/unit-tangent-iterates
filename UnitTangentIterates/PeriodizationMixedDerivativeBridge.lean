import Mathlib
import UnitTangentIterates.PeriodizationDeriv
import UnitTangentIterates.PeriodizationMixedDerivative

/-! # Mixed derivative of the original periodization -/

noncomputable section

open Real

namespace PeriodizationMixedDerivativeBridge

/-- The period derivative, regarded as a function of the spatial point. -/
def periodDerivAt (z : ℝ → ℝ) (H : ℝ) : ℝ → ℝ := fun s =>
  deriv (fun P => ∑' m : ℤ, z (s - (m : ℝ) * P)) H

/-- The spatial derivative of the period derivative is the mixed termwise
series. -/
theorem hasDerivAt_space_periodDerivAt
    {z z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz01 : ∀ x, HasDerivAt z (z1 x) x)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt (periodDerivAt z H)
      (∑' m : ℤ, (-(m : ℝ)) * z2 (s - (m : ℝ) * H)) s := by
  have heq : periodDerivAt z H = fun x =>
      ∑' m : ℤ, (-(m : ℝ)) * z1 (x - (m : ℝ) * H) := by
    funext x
    have hd := PeriodizationDeriv.hasDerivAt_periodization_period
      (z := z) (z' := z1) (C := C) (a := alpha) (H₀ := H / 2)
      (H := H) (s := x) halpha (by linarith) hz01 hzb hz1b (by linarith)
    exact hd.deriv
  rw [heq]
  exact PeriodizationMixedDerivative.hasDerivAt_space_firstPeriodDerivativeSeries
    halpha hH hz12 hz1b hz2b

/-- Explicit mixed derivative value. -/
theorem mixed_deriv_periodization
    {z z1 z2 : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz01 : ∀ x, HasDerivAt z (z1 x) x)
    (hz12 : ∀ x, HasDerivAt z1 (z2 x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hz1b : ∀ x, |z1 x| ≤ C * Real.exp (-alpha * |x|))
    (hz2b : ∀ x, |z2 x| ≤ C * Real.exp (-alpha * |x|)) :
    deriv (periodDerivAt z H) s =
      ∑' m : ℤ, (-(m : ℝ)) * z2 (s - (m : ℝ) * H) :=
  (hasDerivAt_space_periodDerivAt halpha hH hz01 hz12 hzb hz1b hz2b).deriv

end PeriodizationMixedDerivativeBridge
