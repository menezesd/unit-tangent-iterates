import Mathlib
import UnitTangentIterates.ProfiledInterpolationFields
import UnitTangentIterates.InterpolationPathDist

/-! # Global constants for the profiled interpolation fields -/

noncomputable section

open Function Set

namespace ProfiledInterpolationGlobalBounds

open PathMetricCircle InterpolationPathDist InterpolationEstimate
  ProfiledInterpolationFields

theorem w_le_three_halves (t : ℝ) : w t ≤ (3 / 2 : ℝ) := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [w_eq_of_mem ⟨ht.1.le, ht.2.le⟩]
    nlinarith [sq_nonneg (t - 1 / 2)]
  · rw [w_eq_zero ht]
    norm_num

def globalK (kstar kd dsup L eps : ℝ) : NNReal :=
  Real.toNNReal ((3 / 2) * kstar * interpPathCost kstar kd dsup L eps)

def globalK2 (kstar kd dsup L eps : ℝ) : NNReal :=
  Real.toNNReal ((3 / 2) *
    (kd * costE L eps + kstar * costG1 kstar L eps))

theorem globalK_coe
    {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    (globalK kstar kd dsup L eps : ℝ) =
      (3 / 2) * kstar * interpPathCost kstar kd dsup L eps := by
  rw [globalK, Real.coe_toNNReal]
  have hcost := InterpolationPathDist.interpPathCost_nonneg hkstar hkd hdsup hL heps
  have h32 : (0:ℝ) ≤ 3 / 2 * kstar := by linarith
  exact mul_nonneg h32 hcost

theorem globalK2_coe
    {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    (globalK2 kstar kd dsup L eps : ℝ) =
      (3 / 2) * (kd * costE L eps + kstar * costG1 kstar L eps) := by
  rw [globalK2, Real.coe_toNNReal]
  have h1 : (0:ℝ) ≤ kd * InterpolationPathDist.costE L eps :=
    mul_nonneg hkd (InterpolationPathDist.costE_nonneg hL heps)
  have h2 : (0:ℝ) ≤ kstar * InterpolationPathDist.costG1 kstar L eps :=
    mul_nonneg hkstar (InterpolationPathDist.costG1_nonneg hkstar hL heps)
  have h3 : (0:ℝ) ≤ 3 / 2 := by norm_num
  exact mul_nonneg h3 (by linarith)

theorem abs_hx_le_global
    {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps t s : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hk : |kappa k0 k1 t s| ≤ kstar)
    (hen : |en k0 k1 theta0 L t s| ≤
      w t * interpPathCost kstar kd dsup L eps) :
    |hx k0 k1 theta0 L t s| ≤ (globalK kstar kd dsup L eps : ℝ) := by
  rw [globalK_coe hkstar hkd hdsup hL heps]
  have hw0 := w_nonneg t
  have hw1 := w_le_three_halves t
  have hE := interpPathCost_nonneg hkstar hkd hdsup hL heps
  refine (abs_hx_le hk hen hkstar (mul_nonneg hw0 hE)).trans ?_
  nlinarith [mul_nonneg hkstar hE]

theorem abs_hxx_le_global
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd dsup eps t s : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hkX : |kX k0' k1' t s| ≤ kd)
    (hk : |kappa k0 k1 t s| ≤ kstar)
    (hen : |en k0 k1 theta0 L t s| ≤ w t * costE L eps)
    (henS : |enS k0 k1 theta0 L t s| ≤ w t * costG1 kstar L eps) :
    |hxx k0 k1 k0' k1' theta0 L t s| ≤
      (globalK2 kstar kd dsup L eps : ℝ) := by
  rw [globalK2_coe hkstar hkd hL heps]
  have hw0 := w_nonneg t
  have hw1 := w_le_three_halves t
  have hE0 := costE_nonneg hL heps
  have hE1 := costG1_nonneg hkstar hL heps
  refine (abs_hxx_le hkX hk hen henS hkd hkstar).trans ?_
  nlinarith [mul_nonneg hkd hE0, mul_nonneg hkstar hE1]

/-- A global derivative ceiling gives the canonical scalar Lipschitz constant. -/
theorem lipschitzWith_of_deriv_le_nnreal
    {f f' : ℝ → ℝ} {K : NNReal}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x, |f' x| ≤ (K : ℝ)) : LipschitzWith K f := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hf x).differentiableAt) ?_
  intro x
  rw [(hf x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact hK x

end ProfiledInterpolationGlobalBounds
