import Mathlib
import UnitTangentIterates.PeriodizationFiniteWeight

/-! # Finite mixed derivative chains for translated summands -/

noncomputable section

namespace PeriodizationFiniteDerivativeChain

/-- A compatible family of ordinary derivatives of a pulse. -/
structure DerivativeChain (zD : ℕ → ℝ → ℝ) : Prop where
  deriv : ∀ n x, HasDerivAt (zD n) (zD (n + 1) x) x

/-- The summand predicted by the TeX formula after `r` spatial and `q` period
derivatives. -/
def mixedTerm (zD : ℕ → ℝ → ℝ) (r q : ℕ) (s : ℝ) (m : ℤ) (H : ℝ) : ℝ :=
  (-(m : ℝ)) ^ q * zD (r + q) (s - (m : ℝ) * H)

/-- One further period derivative multiplies by `-m` and advances the pulse
derivative order. -/
theorem hasDerivAt_mixedTerm_period
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    (r q : ℕ) (s : ℝ) (m : ℤ) (H : ℝ) :
    HasDerivAt (mixedTerm zD r q s m)
      (mixedTerm zD r (q + 1) s m H) H := by
  have hin : HasDerivAt (fun P : ℝ => s - (m : ℝ) * P) (-(m : ℝ)) H := by
    convert (hasDerivAt_const H s).sub
      ((hasDerivAt_const H (m : ℝ)).mul (hasDerivAt_id H)) using 1 <;> ring
  have hc := (hz.deriv (r + q) (s - (m : ℝ) * H)).comp H hin
  convert (hasDerivAt_const H ((-(m : ℝ)) ^ q)).mul hc using 1 <;>
    simp [mixedTerm] <;> ring

/-- One further spatial derivative advances the pulse derivative order but
does not introduce another translation-index factor. -/
theorem hasDerivAt_mixedTerm_space
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    (r q : ℕ) (s : ℝ) (m : ℤ) (H : ℝ) :
    HasDerivAt (fun x => mixedTerm zD r q x m H)
      (mixedTerm zD (r + 1) q s m H) s := by
  have hc := (hz.deriv (r + q) (s - (m : ℝ) * H)).comp s
    ((hasDerivAt_id s).sub_const ((m : ℝ) * H))
  refine ((hasDerivAt_const s ((-(m : ℝ)) ^ q)).mul hc).congr_deriv ?_
  simp only [mixedTerm, Nat.add_right_comm r 1 q]
  ring

/-- Pointwise absolute value of a mixed summand has precisely the polynomial
weight used by `PeriodizationFiniteWeight`. -/
theorem abs_mixedTerm (zD : ℕ → ℝ → ℝ) (r q : ℕ)
    (s : ℝ) (m : ℤ) (H : ℝ) :
    |mixedTerm zD r q s m H| =
      |(m : ℝ)| ^ q * |zD (r + q) (s - (m : ℝ) * H)| := by
  simp [mixedTerm, abs_mul, abs_pow]

end PeriodizationFiniteDerivativeChain
