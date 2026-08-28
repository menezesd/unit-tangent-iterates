import UnitTangentIterates.NearIdentityDistortionBudget

/-!
# Near-identity distortion budgets from a summable majorant

Finite pullback columns naturally produce their actual gauge error only while
the column is being constructed.  The scalar construction instead supplies a
fixed summable majorant.  This adapter records that the latter is sufficient
for the distortion budget used by the stable-component recurrence.
-/

noncomputable section

open MeasureTheory

namespace NearIdentityDistortionBudgetMajorant

open AnchoredJacobiStableTransition NearIdentityDistortionBudget

/-- Any nonnegative error sequence below a summable half-sized majorant has
the same aggregate near-identity distortion budget as that majorant. -/
def budgetOfMajorant
    {eps major : ℕ → ℝ} {E : ℝ}
    (heps : ∀ j, 0 ≤ eps j)
    (hmajorHalf : ∀ j, major j ≤ 1 / 2)
    (hsum : Summable major)
    (htsum : (∑' j, major j) ≤ E)
    (hle : ∀ j, eps j ≤ major j) :
    DistortionBudget (invLower eps) (upper eps) eps (2 * E) E E := by
  have hepsHalf : ∀ j, eps j ≤ 1 / 2 := fun j ↦
    (hle j).trans (hmajorHalf j)
  have hepsSummable : Summable eps :=
    hsum.of_nonneg_of_le heps hle
  have hepsTsum : (∑' j, eps j) ≤ E :=
    (hepsSummable.tsum_le_tsum hle hsum).trans htsum
  exact budget heps hepsHalf hepsSummable hepsTsum

end NearIdentityDistortionBudgetMajorant
