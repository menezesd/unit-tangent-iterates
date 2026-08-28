import Mathlib
import UnitTangentIterates.PeriodizationPositiveMixedSteps

/-! # Local finite mixed-derivative certificates on positive periods -/

noncomputable section

namespace PeriodizationPositiveMixedCertificate

open PeriodizationFiniteDerivativeChain PeriodizationPositiveMixedSteps

/-- The exact mixed derivative candidate at order `(r,q)`. -/
def mixedSum (zD : ℕ → ℝ → ℝ) (r q : ℕ) (s H : ℝ) : ℝ :=
  ∑' m : ℤ, mixedTerm zD r q s m H

/-- A local derivative node on the open positive-period domain.  It records
the exact TeX formula and both outgoing derivative transitions. -/
structure PositiveMixedDerivativeCertificate
    (zD : ℕ → ℝ → ℝ) (r q : ℕ) : Prop where
  formula : ∀ s H, 0 < H → mixedSum zD r q s H =
    ∑' m : ℤ, (-(m : ℝ)) ^ q * zD (r + q) (s - (m : ℝ) * H)
  periodTransition : ∀ s H, 0 < H →
    HasDerivAt (fun P => mixedSum zD r q s P)
      (mixedSum zD r (q + 1) s H) H
  spaceTransition : ∀ s H, 0 < H →
    HasDerivAt (fun x => mixedSum zD r q x H)
      (mixedSum zD (r + 1) q s H) s

/-- Every finite mixed order has a local certificate once the two positive
recursion steps are available. -/
theorem exists_certificate
    {zD : ℕ → ℝ → ℝ} (h : PositiveMixedTsumDerivativeSteps zD)
    (r q : ℕ) : PositiveMixedDerivativeCertificate zD r q := by
  refine ⟨?_, ?_, ?_⟩
  · intro s H _
    rfl
  · intro s H hH
    simpa [mixedSum] using h.periodStep r q s H hH
  · intro s H hH
    simpa [mixedSum] using h.spaceStep r q s H hH

/-- All-order exponential derivative bounds produce a certificate at every
finite pair `(r,q)`. -/
theorem exists_certificate_of_exp
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} {alpha : ℝ} (halpha : 0 < alpha)
    (hb : ∀ n x, |zD n x| ≤ C n * Real.exp (-alpha * |x|)) :
    ∀ r q : ℕ, PositiveMixedDerivativeCertificate zD r q := by
  have hsteps := exists_positiveMixedTsumDerivativeSteps hz halpha hb
  exact fun r q => exists_certificate hsteps r q

end PeriodizationPositiveMixedCertificate
