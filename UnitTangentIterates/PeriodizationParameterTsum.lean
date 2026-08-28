import Mathlib
import UnitTangentIterates.PeriodizationParameterDerivative

/-!
# Termwise differentiation of a periodization in its period

This is the interchange step in the proof of TeX Lemma `lem:periodization`.
The spatial point is fixed and the period varies in an open interval.
-/

noncomputable section

open Real Set

namespace PeriodizationParameterTsum

/-- A locally uniform summable majorant for the differentiated translates
justifies differentiating the bilateral periodization with respect to `H`. -/
theorem hasDerivAt_tsum_period
    {z zd : ℝ → ℝ} {s H0 rho : ℝ} {M : ℤ → ℝ}
    (hrho : 0 < rho)
    (hz : ∀ x, HasDerivAt z (zd x) x)
    (hM : Summable M)
    (hMbound : ∀ (m : ℤ) (H : ℝ), H ∈ Ioo (H0 - rho) (H0 + rho) →
      ‖-(m : ℝ) * zd (s - (m : ℝ) * H)‖ ≤ M m)
    (hsum : Summable fun m : ℤ => z (s - (m : ℝ) * H0)) :
    HasDerivAt (fun H => ∑' m : ℤ, z (s - (m : ℝ) * H))
      (∑' m : ℤ, -(m : ℝ) * zd (s - (m : ℝ) * H0)) H0 := by
  let U : Set ℝ := Ioo (H0 - rho) (H0 + rho)
  have hH0 : H0 ∈ U := by
    constructor <;> dsimp [U] <;> linarith
  have hderiv : ∀ (m : ℤ), ∀ H ∈ U,
      HasDerivAt (fun h => z (s - (m : ℝ) * h))
        (-(m : ℝ) * zd (s - (m : ℝ) * H)) H := by
    intro m H _
    exact PeriodizationParameterDerivative.hasDerivAt_period_translate_int hz s H m
  exact hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv (by simpa [U] using hMbound) hH0 hsum hH0

/-- Absolute-value form of the derivative series, convenient for inserting
the exponential-polynomial majorant from the TeX proof. -/
theorem norm_period_derivative_term
    (zd : ℝ → ℝ) (s H : ℝ) (m : ℤ) :
    ‖-(m : ℝ) * zd (s - (m : ℝ) * H)‖ =
      |(m : ℝ)| * |zd (s - (m : ℝ) * H)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_neg]

end PeriodizationParameterTsum
