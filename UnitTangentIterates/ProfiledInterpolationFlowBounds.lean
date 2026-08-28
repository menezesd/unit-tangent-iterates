import Mathlib
import UnitTangentIterates.FlowDerivativeTimeChange
import UnitTangentIterates.InterpolationVariableSpeedConstants
import UnitTangentIterates.InterpolationControlledJunctionFinal

/-! # Quantitative variational bounds for the profiled interpolation flow -/

noncomputable section

open Function

namespace ProfiledInterpolationFlowBounds

open FlowDerivative GaugeFlowTimeDerivative InterpolationPathDist
  InterpolationFrame InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal PathMetricCircle

theorem flowDeriv_le
    {hx : ℝ → ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    {kstar L eps t u : ℝ}
    (hkstar : 0 ≤ kstar) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hgc : Continuous fun s => hx s (Phi s u))
    (hraw : ∀ a v, flowDeriv hx Phi (2 * L) a v ≤
      2 * L * Real.exp (rate1Bound kstar L eps * |a|)) :
    flowDeriv (fun r x => w r * hx (B r) x)
        (fun r v => Phi (B r) v) (2 * L) t u ≤ costFac kstar L eps := by
  rw [FlowDerivativeTimeChange.flowDeriv_comp B_zero hasDerivAt_B continuous_w hgc]
  refine (hraw (B t) u).trans ?_
  unfold costFac
  gcongr
  have habs : |B t| ≤ 1 := by rw [abs_of_nonneg (B_nonneg t)]; exact B_le_one t
  have h1 := rate1Bound_nonneg hkstar hL heps
  nlinarith [abs_nonneg (B t)]

theorem flowDeriv2_le
    {hx hxx : ℝ → ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    {kstar kd L eps t u : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hxgc : Continuous fun s => hx s (Phi s u))
    (hxxgc : Continuous fun s => hxx s (Phi s u))
    (hFgc : Continuous fun s => flowDeriv hx Phi (2 * L) s u)
    (hraw : ∀ a v, |flowDeriv2 hx hxx Phi (2 * L) a v| ≤
      rate2Bound kstar kd L eps * (2 * L) ^ 2 * |a| *
        Real.exp (2 * rate1Bound kstar L eps * |a|)) :
    |flowDeriv2 (fun r x => w r * hx (B r) x)
        (fun r x => w r * hxx (B r) x)
        (fun r v => Phi (B r) v) (2 * L) t u| ≤
      interpolationG1 kstar kd L eps := by
  rw [FlowDerivativeTimeChange.flowDeriv2_comp B_zero hasDerivAt_B continuous_w
    hxgc hxxgc hFgc]
  refine (hraw (B t) u).trans ?_
  have hB0 := B_nonneg t
  have hB1 := B_le_one t
  have habs : |B t| ≤ 1 := by rw [abs_of_nonneg hB0]; exact hB1
  unfold interpolationG1
  have hr2 : 0 ≤ rate2Bound kstar kd L eps :=
    rate2Bound_nonneg hkstar hkd hL heps
  have hA : 0 ≤ rate2Bound kstar kd L eps * (2 * L) ^ 2 :=
    mul_nonneg hr2 (sq_nonneg _)
  exact mul_le_mul
    (mul_le_of_le_one_right hA habs)
    (Real.exp_le_exp.mpr
      (by nlinarith [rate1Bound_nonneg hkstar hL heps, habs, abs_nonneg (B t)]))
    (Real.exp_pos _).le hA

theorem field1_cost
    {kstar kd dsup L eps t x : ℝ} {m : ℝ → ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hm : m t = w t * interpPathCost kstar kd dsup L eps)
    (hfield : |x| ≤ w t * rate1Bound kstar L eps) :
    |x| * costFac kstar L eps ≤
      (4 * kstar) * costFac kstar L eps * m t := by
  rw [hm]
  have hr := rate1Bound_le_mul_cost hkstar hkd hdsup hL heps
  have hw := w_nonneg t
  have hP : 0 ≤ costFac kstar L eps := costFac_nonneg hL
  calc
    |x| * costFac kstar L eps ≤
        (w t * rate1Bound kstar L eps) * costFac kstar L eps :=
      mul_le_mul_of_nonneg_right hfield hP
    _ ≤ (w t * (4 * kstar * interpPathCost kstar kd dsup L eps)) *
        costFac kstar L eps := by gcongr
    _ = (4 * kstar) * costFac kstar L eps *
        (w t * interpPathCost kstar kd dsup L eps) := by ring

theorem field2_cost
    {kstar kd dsup L eps t x xx : ℝ} {m : ℝ → ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 < L) (heps : 0 ≤ eps)
    (hm : m t = w t * interpPathCost kstar kd dsup L eps)
    (hfield1 : |x| ≤ w t * rate1Bound kstar L eps)
    (hfield2 : |xx| ≤ w t * rate2Bound kstar kd L eps) :
    |x| * interpolationG1 kstar kd L eps +
        |xx| * costFac kstar L eps ^ 2 ≤
      interpolationCg kstar kd L eps * m t := by
  rw [hm]
  have hmix := mixed_rate_le_interpolationCg_mul_cost
    hkstar hkd hdsup hL heps
  have hw := w_nonneg t
  have hG : 0 ≤ interpolationG1 kstar kd L eps := by
    unfold interpolationG1
    have := rate2Bound_nonneg hkstar hkd hL.le heps
    positivity
  have hP : 0 ≤ costFac kstar L eps ^ 2 := sq_nonneg _
  calc
    |x| * interpolationG1 kstar kd L eps + |xx| * costFac kstar L eps ^ 2
        ≤ (w t * rate1Bound kstar L eps) * interpolationG1 kstar kd L eps +
          (w t * rate2Bound kstar kd L eps) * costFac kstar L eps ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hfield1 hG)
        (mul_le_mul_of_nonneg_right hfield2 hP)
    _ = w t * (rate1Bound kstar L eps * interpolationG1 kstar kd L eps +
          rate2Bound kstar kd L eps * costFac kstar L eps ^ 2) := by ring
    _ ≤ w t * (interpolationCg kstar kd L eps *
          interpPathCost kstar kd dsup L eps) :=
      mul_le_mul_of_nonneg_left hmix hw
    _ = interpolationCg kstar kd L eps *
          (w t * interpPathCost kstar kd dsup L eps) := by ring

theorem sharp_field_costs
    {kstar kd L eps m m1 x xx : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hm : 0 ≤ m) (hm1 : 0 ≤ m1)
    (hx : |x| ≤ kstar * m)
    (hxx : |xx| ≤ kd * m + kstar * m1)
    (hm1P : m1 * costFac kstar L eps ≤ m) :
    |x| * interpolationG1 kstar kd L eps +
        |xx| * costFac kstar L eps ^ 2 ≤
      interpolationCgFinal kstar kd L eps * m := by
  have hP : 0 ≤ costFac kstar L eps := costFac_nonneg hL
  have hG : 0 ≤ interpolationG1 kstar kd L eps := by
    unfold interpolationG1
    have := rate2Bound_nonneg hkstar hkd hL heps
    positivity
  have hx' := mul_le_mul_of_nonneg_right hx hG
  have hxx' := mul_le_mul_of_nonneg_right hxx (sq_nonneg (costFac kstar L eps))
  have hm1' : m1 * costFac kstar L eps ^ 2 ≤
      m * costFac kstar L eps := by
    calc
      m1 * costFac kstar L eps ^ 2 =
          (m1 * costFac kstar L eps) * costFac kstar L eps := by ring
      _ ≤ m * costFac kstar L eps :=
        mul_le_mul_of_nonneg_right hm1P hP
  have hsharp := sharpCg_le_final kstar kd L eps
  calc
    |x| * interpolationG1 kstar kd L eps + |xx| * costFac kstar L eps ^ 2
        ≤ (kstar * m) * interpolationG1 kstar kd L eps +
          (kd * m + kstar * m1) * costFac kstar L eps ^ 2 :=
      add_le_add hx' hxx'
    _ ≤ (kstar * interpolationG1 kstar kd L eps +
          kd * costFac kstar L eps ^ 2 + kstar * costFac kstar L eps) * m := by
      nlinarith
    _ ≤ interpolationCgFinal kstar kd L eps * m :=
      mul_le_mul_of_nonneg_right hsharp hm

end ProfiledInterpolationFlowBounds
