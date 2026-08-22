import Mathlib
import UnitTangentIterates.Periodization
import UnitTangentIterates.FrontPeriodizationIntegral

/-!
# A sup bound for the periodization

The estimates of *A Noncircular Oval with Convex Unit-Tangent Iterates* that
concern the periodized profile `Y_P(u) = ∑_{m∈ℤ} y(u - mP)` all require it to
stay below a threshold `a < 1`.  `UnitTangentIterates/Periodization.lean` bounds the
periodization error `|Y_P - y|` on the **centred cell**; since the
periodization is `P`-periodic, that cell bound gives a bound at every point.

Main result: `periodization_le_of_sup`, `Y_P ≤ b + 4Ce^{-(α/2)P}` everywhere,
for a nonnegative pulse bounded by `b` and by `Ce^{-α|·|}`.
-/

noncomputable section

open Real Set

namespace PeriodizationSup

variable {y : ℝ → ℝ} {C alpha P b : ℝ}

/-- **A sup bound for the periodization.**  If the pulse is nonnegative,
bounded by `b` and exponentially localized, then its periodization of period
`P` satisfies `Y_P(u) ≤ b + 4Ce^{-(α/2)P}` at every point. -/
theorem periodization_le_of_sup (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ x, 0 ≤ y x) (hyb : ∀ x, y x ≤ C * Real.exp (-alpha * |x|))
    (hsup : ∀ x, y x ≤ b) (u : ℝ) :
    (∑' m : ℤ, y (u - m * P)) ≤ b + 4 * C * Real.exp (-(alpha / 2) * P) := by
  have hcell : ∀ v : ℝ, |v| ≤ P / 2 →
      (∑' m : ℤ, y (v - m * P)) ≤ b + 4 * C * Real.exp (-(alpha / 2) * P) := by
    intro v hv
    have herr := Periodization.periodization_error_le (z := y) (C := C) (a := alpha)
      (H := P) (s := v) halpha hy0 hyb hP hq hv
    have h1 : (∑' m : ℤ, y (v - m * P)) - y v ≤ 4 * C * Real.exp (-(alpha / 2) * P) :=
      le_trans (le_abs_self _) herr
    have h2 := hsup v
    linarith
  have hper : Function.Periodic (fun w => ∑' m : ℤ, y (w - m * P)) P :=
    FrontPeriodizationIntegral.periodic_tsum_translates y P
  obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP u
  rw [show (∑' m : ℤ, y (u - m * P)) = ∑' m : ℤ, y (v - m * P) from heq]
  rcases le_or_gt v (P / 2) with h | h
  · exact hcell v (by rw [abs_of_nonneg hv.1]; exact h)
  · have hshift := hper (v - P)
    simp only [sub_add_cancel] at hshift
    rw [hshift]
    refine hcell (v - P) ?_
    have h2 := hv.2
    rw [abs_le]
    constructor <;> linarith

end PeriodizationSup
