import UnitTangentIterates.AnchoredJacobiStableTransition

/-!
# Distortion budgets from summable near-identity markings

A normalized marking whose first derivative differs from one by at most
`eps k` and whose second derivative is bounded by `eps k` has junction
parameters `1-eps k`, `1+eps k`, and `eps k`.  Under `eps k <= 1/2`, the
inverse lower-Jacobian excess is at most `2*eps k`.  Thus one summable jet
error controls all three distortion series used by the stable Jacobi
transition.
-/

noncomputable section

open MeasureTheory

namespace NearIdentityDistortionBudget

open AnchoredJacobiStableTransition

def invLower (eps : ℕ → ℝ) (k : ℕ) : ℝ := 1 / (1 - eps k)
def upper (eps : ℕ → ℝ) (k : ℕ) : ℝ := 1 + eps k

theorem invLower_sub_one_nonnegative
    {eps : ℕ → ℝ} (heps0 : ∀ k, 0 ≤ eps k)
    (hepsHalf : ∀ k, eps k ≤ 1 / 2) (k : ℕ) :
    0 ≤ invLower eps k - 1 := by
  have hden : 0 < 1 - eps k := by linarith [hepsHalf k]
  have hle : 1 ≤ 1 / (1 - eps k) := by
    rw [le_div_iff₀ hden]
    linarith [heps0 k]
  simpa [invLower] using sub_nonneg.mpr hle

theorem invLower_sub_one_le
    {eps : ℕ → ℝ} (heps0 : ∀ k, 0 ≤ eps k)
    (hepsHalf : ∀ k, eps k ≤ 1 / 2) (k : ℕ) :
    invLower eps k - 1 ≤ 2 * eps k := by
  have hden : 0 < 1 - eps k := by linarith [hepsHalf k]
  rw [show invLower eps k - 1 = eps k / (1 - eps k) by
    dsimp [invLower]
    field_simp
    ring]
  rw [div_le_iff₀ hden]
  have hfactor : 0 ≤ eps k * (1 - 2 * eps k) :=
    mul_nonneg (heps0 k) (by linarith [hepsHalf k])
  nlinarith

/-- A single summable near-identity jet bound supplies the complete stable
distortion budget. -/
def budget
    {eps : ℕ → ℝ} {E : ℝ}
    (heps0 : ∀ k, 0 ≤ eps k)
    (hepsHalf : ∀ k, eps k ≤ 1 / 2)
    (heps : Summable eps) (htsum : (∑' k, eps k) ≤ E) :
    DistortionBudget (invLower eps) (upper eps) eps (2 * E) E E := by
  have hinvSum : Summable (fun k => invLower eps k - 1) :=
    (heps.mul_left 2).of_nonneg_of_le
      (fun k => invLower_sub_one_nonnegative heps0 hepsHalf k)
      (fun k => invLower_sub_one_le heps0 hepsHalf k)
  refine
    { a_one := ?_
      MA_one := ?_
      NA_nonnegative := heps0
      Aw_nonnegative := ?_
      AM_nonnegative := ?_
      AN_nonnegative := ?_
      summable_a := hinvSum
      summable_MA := ?_
      summable_NA := heps
      tsum_a_le := ?_
      tsum_MA_le := ?_
      tsum_NA_le := htsum }
  · intro k
    exact sub_nonneg.mp (invLower_sub_one_nonnegative heps0 hepsHalf k)
  · intro k
    simp [upper, heps0 k]
  · have hE : 0 ≤ E := (tsum_nonneg heps0).trans htsum
    positivity
  · exact (tsum_nonneg heps0).trans htsum
  · exact (tsum_nonneg heps0).trans htsum
  · simpa [upper] using heps
  · have hle := hinvSum.tsum_le_tsum
      (fun k => invLower_sub_one_le heps0 hepsHalf k)
      (heps.mul_left 2)
    calc
      (∑' k, (invLower eps k - 1)) ≤ ∑' k, 2 * eps k := hle
      _ = 2 * (∑' k, eps k) := tsum_mul_left
      _ ≤ 2 * E := mul_le_mul_of_nonneg_left htsum (by norm_num)
  · simpa [upper] using htsum

end NearIdentityDistortionBudget
