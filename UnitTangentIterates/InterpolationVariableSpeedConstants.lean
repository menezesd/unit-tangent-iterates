import Mathlib
import UnitTangentIterates.InterpolationCostAggregation

/-! # Explicit variable-speed constants for curvature interpolation -/

noncomputable section

namespace InterpolationVariableSpeedConstants

open InterpolationPathDist InterpolationFrame InterpolationNormal

def rate2LinearCoeff (kstar kd L : ℝ) : ℝ :=
  4 * kd + 16 * kstar ^ 2 + 8 * kstar / (3 * L)

def interpolationCg (kstar kd L eps : ℝ) : ℝ :=
  4 * kstar *
      (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
        Real.exp (2 * rate1Bound kstar L eps)) +
    rate2LinearCoeff kstar kd L * costFac kstar L eps ^ 2

def interpolationCgFinal (kstar kd L eps : ℝ) : ℝ :=
  max (interpolationCg kstar kd L eps)
    (kstar * (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
        Real.exp (2 * rate1Bound kstar L eps)) +
      kd * costFac kstar L eps ^ 2 + kstar * costFac kstar L eps)

theorem interpolationCg_le_final (kstar kd L eps : ℝ) :
    interpolationCg kstar kd L eps ≤ interpolationCgFinal kstar kd L eps :=
  le_max_left _ _

theorem sharpCg_le_final (kstar kd L eps : ℝ) :
    kstar * (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
        Real.exp (2 * rate1Bound kstar L eps)) +
        kd * costFac kstar L eps ^ 2 + kstar * costFac kstar L eps ≤
      interpolationCgFinal kstar kd L eps :=
  le_max_right _ _

theorem interpolationCgFinal_nonneg {kstar kd L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    0 ≤ interpolationCgFinal kstar kd L eps := by
  apply le_trans ?_ (sharpCg_le_final kstar kd L eps)
  have hr2 := rate2Bound_nonneg hkstar hkd hL heps
  have hfac := costFac_nonneg (kstar := kstar) (eps := eps) hL
  positivity

def frameD (kstar kd L eps : ℝ) : ℝ :=
  1 + 1 / costFac kstar L eps + 2 * kstar +
    1 / costFac kstar L eps ^ 2 + kstar ^ 2 + 2 * kd

def interpolationP0 (kstar kd L eps : ℝ) : ℝ :=
  1 / frameD kstar kd L eps

theorem costG1_mul_costFac_le {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costG1 kstar L eps * costFac kstar L eps ≤
      interpPathCost kstar kd dsup L eps := by
  simpa [costTermS1] using
    costTermS1_le_interpPathCost hkstar hkd hdsup hL heps

theorem costG2_mul_costFac_sq_le {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costG2 kstar kd dsup L eps * costFac kstar L eps ^ 2 ≤
      interpPathCost kstar kd dsup L eps := by
  have hsecond : 0 ≤ costG1 kstar L eps *
      (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
        Real.exp (2 * rate1Bound kstar L eps)) := by
    exact mul_nonneg (costG1_nonneg hkstar hL heps)
      (mul_nonneg (mul_nonneg (rate2Bound_nonneg hkstar hkd hL heps)
        (sq_nonneg _)) (Real.exp_pos _).le)
  have hterm := costTermS2_le_interpPathCost
    (kstar := kstar) (kd := kd) (dsup := dsup) hkstar hL heps
  unfold costTermS2 at hterm
  linarith

theorem rate1Bound_le_mul_cost {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    rate1Bound kstar L eps ≤
      4 * kstar * interpPathCost kstar kd dsup L eps := by
  have hE := costE_le_interpPathCost hkstar hkd hdsup hL heps
  simpa [rate1Bound, costE] using
    mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 4 * kstar)

theorem rate2LinearCoeff_nonneg {kstar kd L : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) :
    0 ≤ rate2LinearCoeff kstar kd L := by
  unfold rate2LinearCoeff
  positivity

theorem rate2Bound_le_mul_cost {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 < L) (heps : 0 ≤ eps) :
    rate2Bound kstar kd L eps ≤
      rate2LinearCoeff kstar kd L *
        interpPathCost kstar kd dsup L eps := by
  have hE := costE_le_interpPathCost hkstar hkd hdsup hL.le heps
  have hc : 0 ≤ rate2LinearCoeff kstar kd L :=
    rate2LinearCoeff_nonneg hkstar hkd hL
  have heq : eps = (2 / (3 * L)) * costE L eps := by
    unfold costE
    field_simp
  have hrw : rate2Bound kstar kd L eps =
      rate2LinearCoeff kstar kd L * costE L eps := by
    rw [heq]
    unfold rate2Bound rate2LinearCoeff costE
    field_simp
    ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hE hc

theorem mixed_rate_le_interpolationCg_mul_cost
    {kstar kd dsup L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 < L) (heps : 0 ≤ eps) :
    rate1Bound kstar L eps *
        (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
          Real.exp (2 * rate1Bound kstar L eps)) +
      rate2Bound kstar kd L eps * costFac kstar L eps ^ 2 ≤
      interpolationCg kstar kd L eps *
        interpPathCost kstar kd dsup L eps := by
  have h1 := rate1Bound_le_mul_cost hkstar hkd hdsup hL.le heps
  have h2 := rate2Bound_le_mul_cost hkstar hkd hdsup hL heps
  have hG : 0 ≤ rate2Bound kstar kd L eps * (2 * L) ^ 2 *
      Real.exp (2 * rate1Bound kstar L eps) := by
    exact mul_nonneg (mul_nonneg (rate2Bound_nonneg hkstar hkd hL.le heps)
      (sq_nonneg _)) (Real.exp_pos _).le
  have hP : 0 ≤ costFac kstar L eps ^ 2 := sq_nonneg _
  have ha := mul_le_mul_of_nonneg_right h1 hG
  have hb := mul_le_mul_of_nonneg_right h2 hP
  unfold interpolationCg
  nlinarith

theorem costFac_pos {kstar L eps : ℝ} (hL : 0 < L) :
    0 < costFac kstar L eps := by
  unfold costFac
  positivity

theorem frameD_pos {kstar kd L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) :
    0 < frameD kstar kd L eps := by
  have hP := costFac_pos (kstar := kstar) (eps := eps) hL
  unfold frameD
  positivity

theorem interpolationP0_pos {kstar kd L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) :
    0 < interpolationP0 kstar kd L eps := by
  exact one_div_pos.mpr (frameD_pos hkstar hkd hL)

theorem frame_angle_numerical {kstar kd L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) :
    1 / costFac kstar L eps + 2 * kstar ≤
      1 / interpolationP0 kstar kd L eps := by
  have hD := frameD_pos (eps := eps) hkstar hkd hL
  rw [interpolationP0, one_div_div]
  unfold frameD
  have hP := costFac_pos (kstar := kstar) (eps := eps) hL
  have hInv : 0 ≤ 1 / costFac kstar L eps := one_div_nonneg.mpr hP.le
  have hInvSq : 0 ≤ 1 / costFac kstar L eps ^ 2 :=
    div_nonneg (by norm_num) (sq_nonneg _)
  simp only [div_one]
  nlinarith [sq_nonneg kstar]

theorem frame_curvature_numerical {kstar kd L eps : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) :
    1 / costFac kstar L eps ^ 2 + kstar ^ 2 + 2 * kd ≤
      1 / interpolationP0 kstar kd L eps ^ 2 + kstar ^ 2 := by
  have hD := frameD_pos (eps := eps) hkstar hkd hL
  have hP := costFac_pos (kstar := kstar) (eps := eps) hL
  have hInv : 0 ≤ 1 / costFac kstar L eps := one_div_nonneg.mpr hP.le
  have hInvSq : 0 ≤ 1 / costFac kstar L eps ^ 2 :=
    div_nonneg (by norm_num) (sq_nonneg _)
  rw [interpolationP0]
  have hbase : 1 / costFac kstar L eps ^ 2 + 2 * kd ≤
      frameD kstar kd L eps := by
    unfold frameD
    nlinarith [sq_nonneg kstar]
  have hDone : 1 ≤ frameD kstar kd L eps := by
    unfold frameD
    nlinarith [sq_nonneg kstar]
  have hsquare : 1 / costFac kstar L eps ^ 2 + 2 * kd ≤
      frameD kstar kd L eps ^ 2 := by nlinarith
  simp only [one_div, inv_pow, inv_inv] at hsquare ⊢
  nlinarith

end InterpolationVariableSpeedConstants
