import Mathlib
import UnitTangentIterates.PeriodizationDeriv

/-!
# Paper-facing period-parameter derivative

`PeriodizationDeriv.hasDerivAt_periodization_period` already proves the full
majorant/interchange theorem.  This file records the direct specialization
used in TeX Lemma `lem:periodization`, choosing the admissible lower period
`H/2` at the period `H` under consideration.
-/

noncomputable section

namespace PeriodizationParameterExponential

/-- Holding `s` fixed, an exponentially decaying pulse periodization is
differentiable in every positive period.  The derivative is the termwise
series `sum_m -m z'(s-mH)`. -/
theorem hasDerivAt_periodization_period_of_pos
    {z zd : ℝ → ℝ} {C alpha H s : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hz : ∀ x, HasDerivAt z (zd x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-alpha * |x|))
    (hzdb : ∀ x, |zd x| ≤ C * Real.exp (-alpha * |x|)) :
    HasDerivAt (fun P => ∑' m : ℤ, z (s - (m : ℝ) * P))
      (∑' m : ℤ, (-(m : ℝ)) * zd (s - (m : ℝ) * H)) H := by
  have hhalf : 0 < H / 2 := by linarith
  have hlt : H / 2 < H := by linarith
  exact PeriodizationDeriv.hasDerivAt_periodization_period
    (z := z) (z' := zd) (C := C) (a := alpha) (H₀ := H / 2)
    (H := H) (s := s) halpha hhalf hz hzb hzdb hlt

end PeriodizationParameterExponential
