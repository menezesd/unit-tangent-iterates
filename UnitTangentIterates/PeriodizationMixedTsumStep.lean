import Mathlib
import UnitTangentIterates.PeriodizationFiniteDerivativeChain

/-! # One period-direction interchange step for mixed periodization terms -/

noncomputable section

open Set

namespace PeriodizationMixedTsumStep

open PeriodizationFiniteDerivativeChain

/-- Under a locally uniform summable majorant, one may differentiate the
mixed-term series once more in the period direction. -/
theorem hasDerivAt_tsum_mixedTerm_period
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    (r q : ℕ) (s H rho : ℝ) {M : ℤ → ℝ}
    (hrho : 0 < rho)
    (hM : Summable M)
    (hbound : ∀ (m : ℤ) (P : ℝ), P ∈ Ioo (H - rho) (H + rho) →
      ‖mixedTerm zD r (q + 1) s m P‖ ≤ M m)
    (hbase : Summable fun m : ℤ => mixedTerm zD r q s m H) :
    HasDerivAt
      (fun P => ∑' m : ℤ, mixedTerm zD r q s m P)
      (∑' m : ℤ, mixedTerm zD r (q + 1) s m H) H := by
  let U : Set ℝ := Ioo (H - rho) (H + rho)
  have hHU : H ∈ U := by
    constructor <;> dsimp [U] <;> linarith
  have hd : ∀ (m : ℤ) (P : ℝ), P ∈ U →
      HasDerivAt (mixedTerm zD r q s m)
        (mixedTerm zD r (q + 1) s m P) P := by
    intro m P _
    exact hasDerivAt_mixedTerm_period hz r q s m P
  exact hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hd (by simpa [U] using hbound) hHU hbase hHU

end PeriodizationMixedTsumStep
