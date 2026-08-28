import Mathlib
import UnitTangentIterates.PeriodizationFiniteDerivativeChain
import UnitTangentIterates.PeriodizationMixedTsumStep

/-! # Space-direction interchange and induction-ready mixed steps -/

noncomputable section

open Set

namespace PeriodizationMixedTsumSpaceStep

open PeriodizationFiniteDerivativeChain

/-- Under a locally uniform summable majorant, one may differentiate the
mixed-term series once more in the spatial direction. -/
theorem hasDerivAt_tsum_mixedTerm_space
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    (r q : ℕ) (s H rho : ℝ) {M : ℤ → ℝ}
    (hrho : 0 < rho)
    (hM : Summable M)
    (hbound : ∀ (m : ℤ) (x : ℝ), x ∈ Ioo (s - rho) (s + rho) →
      ‖mixedTerm zD (r + 1) q x m H‖ ≤ M m)
    (hbase : Summable fun m : ℤ => mixedTerm zD r q s m H) :
    HasDerivAt
      (fun x => ∑' m : ℤ, mixedTerm zD r q x m H)
      (∑' m : ℤ, mixedTerm zD (r + 1) q s m H) s := by
  let U : Set ℝ := Ioo (s - rho) (s + rho)
  have hsU : s ∈ U := by
    constructor <;> dsimp [U] <;> linarith
  have hd : ∀ (m : ℤ) (x : ℝ), x ∈ U →
      HasDerivAt (fun y => mixedTerm zD r q y m H)
        (mixedTerm zD (r + 1) q x m H) x := by
    intro m x _
    exact hasDerivAt_mixedTerm_space hz r q x m H
  exact hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hd (by simpa [U] using hbound) hsU hbase hsU

/-- An induction-ready certificate containing both mixed derivative recursion
directions for the periodized sums.  No existence is asserted here. -/
structure MixedTsumDerivativeSteps (zD : ℕ → ℝ → ℝ) : Prop where
  periodStep : ∀ r q s H,
    HasDerivAt
      (fun P => ∑' m : ℤ, mixedTerm zD r q s m P)
      (∑' m : ℤ, mixedTerm zD r (q + 1) s m H) H
  spaceStep : ∀ r q s H,
    HasDerivAt
      (fun x => ∑' m : ℤ, mixedTerm zD r q x m H)
      (∑' m : ℤ, mixedTerm zD (r + 1) q s m H) s

end PeriodizationMixedTsumSpaceStep
