import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfJacobiCost
import UnitTangentIterates.GaugeMarkedDataOfNormalRateCircle

/-!
# Non-vacuity of the cost form of the construction

`GaugeMarkedDataOfJacobiCost.exists_variableSpeed_normalPath_of_jacobi_cost`
produces the path `Γ'` of the `C²` comparison from the inverse Jacobi ODE of a
family of rears, with the Lipschitz constant of the gauge field, the bound for
its second space derivative and the two uniform bounds for the flow derivatives
all produced from two density bounds.  This file checks that its hypothesis
block is satisfiable, on the same drifting circle as
`GaugeMarkedDataOfJacobiCircle.lean`: the field of the gauge flow is constant in
the arclength, so both densities vanish and the two comparisons hold with
`κ̂ = 1` and `κ₂ = 0`.

Main result: `exists_variableSpeed_normalPath_driftingCircle_of_jacobi_cost`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfJacobiCostCircle

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeFlowVariableSpeedPathCircle
  GaugeMarkedDataOfJacobiCost GaugeMarkedDataOfNormalRateCircle
  NormalPathC2IncrementVariableSpeed PathMetricCircle

/-- **The drifting circle satisfies the cost form of the hypothesis block**, and
hence produces the normal path with slices of variable speed, with the two
constants of the marking read off the cost. -/
theorem exists_variableSpeed_normalPath_driftingCircle_of_jacobi_cost :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * w t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * w t) ∧
      IsVariableSpeedNormalPath 1
        (costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * w t)) 1
        (costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * w t))
        (1 * costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * w t)
          + 0 * costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * w t) ^ 2) Γ :=
  exists_variableSpeed_normalPath_of_jacobi_cost (Y := Ydrift) (alpha := alphaDrift)
    (k := fun _ _ => 1) (en := fun _ _ => 0) (enS := fun _ _ => 0) (enSS := fun _ _ => 0)
    (g := fun _ _ => 0) (gS := fun _ _ => 0) (h := fun t _ => -w t) (hx := fun _ _ => 0)
    (hxx := fun _ _ => 0) (Phi := PhiDrift) (alphaT := fun t _ => w t)
    (kT := fun _ _ => 0) (kX := fun _ _ => 0) (C := fun _ => 0) (C2 := fun _ => 0)
    (Kx := fun _ => 0) (Rb := w) (S0 := fun _ => 0) (D := fun _ => 0)
    (ell := 2 * Real.pi) (kappa2 := 0) (c := 0) (d := 0) (r := 1 / 2) (kx := 0)
    driftingCircleData.hYC1 driftingCircleData.hY driftingCircleData.hYt
    driftingCircleData.halpha driftingCircleData.hcont
    driftingCircleData.hPhid driftingCircleData.hell driftingCircleData.hPhi0
    driftingCircleData.hxd driftingCircleData.hxcont driftingCircleData.hxxd
    driftingCircleData.hxxcont driftingCircleData.hk le_rfl
    driftingCircleData.hC driftingCircleData.hC2 continuous_const continuous_const
    (fun t => by have := w_nonneg t; simp; linarith) (fun t => by norm_num)
    driftingCircleData.halphaC1
    driftingCircleData.hkC1 driftingCircleData.halphaT driftingCircleData.hkT
    driftingCircleData.hkX driftingCircleData.halphaTc driftingCircleData.hkTc
    driftingCircleData.hkXc driftingCircleData.hkc driftingCircleData.hKxbd
    driftingCircleData.hRbd driftingCircleData.hKxnn
    (fun t x => hasDerivAt_const x (0 : ℝ)) (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun t s => hasDerivAt_const s (w t)) mixed_driftingCircle
    (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun t x => by simpa using hasDerivAt_const x (0 : ℝ))
    (fun t x => by norm_num) (fun t x => by norm_num) (fun t x => by norm_num)
    (fun t => by norm_num) (fun t => by norm_num)
    (fun t => by have := w_nonneg t; linarith) (fun t => le_rfl) (by norm_num)
    (fun t => by have := w_nonneg t; linarith) (by norm_num) (by norm_num)
    driftingCircleData.hT driftingCircleData.hencont driftingCircleData.hstart
    driftingCircleData.hfinish driftingCircleData.hmc driftingCircleData.hmstop
    driftingCircleData.hmbd driftingCircleData.hmsup

end GaugeMarkedDataOfJacobiCostCircle
