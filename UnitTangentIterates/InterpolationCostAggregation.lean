import Mathlib
import UnitTangentIterates.InterpolationPathDist

/-! # Aggregate domination by the interpolation cost density -/

noncomputable section

namespace InterpolationCostAggregation

open InterpolationPathDist InterpolationNormal

/-- All four scalar interpolation densities are simultaneously dominated by
the single paper cost `interpPathCost`. -/
theorem component_bounds
    {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costE L eps ≤ interpPathCost kstar kd dsup L eps ∧
    costTermW kstar L eps ≤ interpPathCost kstar kd dsup L eps ∧
    costTermS1 kstar L eps ≤ interpPathCost kstar kd dsup L eps ∧
    costTermS2 kstar kd dsup L eps ≤ interpPathCost kstar kd dsup L eps := by
  exact ⟨costE_le_interpPathCost hkstar hkd hdsup hL heps,
    costTermW_le_interpPathCost hkstar hkd hdsup hL heps,
    costTermS1_le_interpPathCost hkstar hkd hdsup hL heps,
    costTermS2_le_interpPathCost hkstar hL heps⟩

/-- Multiplication by a nonnegative stopped time profile preserves all four
comparisons.  This is the form consumed with
`m t = w t * interpPathCost ...`. -/
theorem profiled_component_bounds
    {kstar kd dsup L eps : ℝ} {omega : ℝ → ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) (homega : ∀ t, 0 ≤ omega t) :
    ∀ t,
      omega t * costE L eps ≤
          omega t * interpPathCost kstar kd dsup L eps ∧
      omega t * costTermW kstar L eps ≤
          omega t * interpPathCost kstar kd dsup L eps ∧
      omega t * costTermS1 kstar L eps ≤
          omega t * interpPathCost kstar kd dsup L eps ∧
      omega t * costTermS2 kstar kd dsup L eps ≤
          omega t * interpPathCost kstar kd dsup L eps := by
  obtain ⟨h0, hW, h1, h2⟩ :=
    component_bounds hkstar hkd hdsup hL heps
  intro t
  exact ⟨mul_le_mul_of_nonneg_left h0 (homega t),
    mul_le_mul_of_nonneg_left hW (homega t),
    mul_le_mul_of_nonneg_left h1 (homega t),
    mul_le_mul_of_nonneg_left h2 (homega t)⟩

/-- The canonical interpolation density is nonnegative, including at the
stopped endpoints where the profile vanishes. -/
theorem profiled_cost_nonneg
    {kstar kd dsup L eps : ℝ} {omega : ℝ → ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) (homega : ∀ t, 0 ≤ omega t) :
    ∀ t, 0 ≤ omega t * interpPathCost kstar kd dsup L eps := by
  intro t
  exact mul_nonneg (homega t)
    (interpPathCost_nonneg hkstar hkd hdsup hL heps)

end InterpolationCostAggregation
