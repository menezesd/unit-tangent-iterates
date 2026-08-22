import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfNormalRate
import UnitTangentIterates.GaugeFlowVariableSpeedPathCircle

/-!
# Non-vacuity of the gauge-marked data built from the normal rate

`GaugeMarkedDataOfNormalRate.gaugeMarkedData_of_normal_rate` builds the whole
packaged data of a gauge-marked family out of the motion of its slices, the two
bounds on the time derivatives of the frame data being *derived* from the normal
rate through the normal-flow relations rather than assumed.  This file checks
that its hypothesis block is satisfiable, on the drifting circle of
`GaugeFlowVariableSpeedPathCircle.lean`: the unit circle whose arclength phase
`B(t)` runs from `0` to `1`, read in the marking `Φ(t,u) = 2πu − B t` that
follows the drift.

Its normal rate vanishes — the drift is purely tangential — so the sup norms
`S₀, S₁, S₂` are `0`, and the numerical conditions hold with `r = 1/2`: the
field `w` is half the cost density `2w`.  The angle bound the construction
produces is then `0 + κ̂ · R_b = w`, which is exactly the bound supplied by hand
in `driftingCircleData` (`angleRateBound_driftingCircle`).

Main results: `driftingCircleDataOfNormalRate`, `angleRateBound_driftingCircle`,
`exists_variableSpeed_normalPath_driftingCircle_of_normal_rate`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfNormalRateCircle

open GaugeFlowVariableSpeedPath GaugeFlowVariableSpeedPathCircle GaugeFrameTimeBounds
  GaugeMarkedDataOfNormalRate NormalPathC2IncrementVariableSpeed PathMetricCircle

/-- The equality of the mixed partial derivatives for the drifting circle: the
time derivative of its unit tangent and the arclength derivative of its velocity
are both `i w(t) e^{iα}`. -/
theorem mixed_driftingCircle (t s : ℝ) : ∃ W : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (alphaDrift r s : ℂ))) W t ∧
    HasDerivAt (fun x => ((-(-w t) : ℝ) : ℂ) * Complex.exp (Complex.I * (alphaDrift t x : ℂ))
      + ((0 : ℝ) : ℂ) * (Complex.I * Complex.exp (Complex.I * (alphaDrift t x : ℂ)))) W s := by
  refine ⟨Complex.I * ((w t : ℝ) : ℂ) * Complex.exp (Complex.I * (alphaDrift t s : ℂ)), ?_, ?_⟩
  · have halphaT : HasDerivAt (fun r : ℝ => alphaDrift r s) (w t) t := by
      simpa [alphaDrift] using ((hasDerivAt_B t).const_add s).add_const (Real.pi / 2)
    have h1 : HasDerivAt (fun r : ℝ => Complex.I * ((alphaDrift r s : ℝ) : ℂ))
        (Complex.I * ((w t : ℝ) : ℂ)) t := halphaT.ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  · have halphaS : ∀ x : ℝ, HasDerivAt (alphaDrift t) (1 : ℝ) x := fun x => by
      have h : HasDerivAt (fun y : ℝ => y + B t + Real.pi / 2) (1 : ℝ) x :=
        ((hasDerivAt_id x).add_const (B t)).add_const (Real.pi / 2)
      exact h
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * ((alphaDrift t x : ℝ) : ℂ))
        (Complex.I * ((1 : ℝ) : ℂ)) s := (halphaS s).ofReal_comp.const_mul Complex.I
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (alphaDrift t x : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (alphaDrift t s : ℂ))) s := by
      simpa [mul_comm, mul_assoc] using h1.cexp
    have h3 := (h2.const_mul ((-(-w t) : ℝ) : ℂ)).add
      ((h2.const_mul Complex.I).const_mul (((0 : ℝ) : ℂ)))
    refine h3.congr_deriv ?_
    push_cast
    ring

/-- **The drifting circle, with its frame-data bounds produced from its normal
rate.**  The block of `GaugeMarkedDataOfNormalRate.gaugeMarkedData_of_normal_rate`
is satisfiable: no bound on the time derivatives of the tangent angle or of the
curvature is assumed, only the vanishing of the normal rate and the numerical
conditions with `r = 1/2`. -/
def driftingCircleDataOfNormalRate :
    GaugeMarkedData (circleData 1) (circleData 1) 1 (2 * Real.pi) 1 0 0 1
      (fun t => 2 * w t) :=
  gaugeMarkedData_of_normal_rate (Y := Ydrift) (alpha := alphaDrift) (k := fun _ _ => 1)
    (en := fun _ _ => 0) (enS := fun _ _ => 0) (enSS := fun _ _ => 0)
    (h := fun t _ => -w t) (hx := fun _ _ => 0) (hxx := fun _ _ => 0) (Phi := PhiDrift)
    (alphaT := fun t _ => w t) (kT := fun _ _ => 0) (kX := fun _ _ => 0)
    (C := fun _ => 0) (C2 := fun _ => 0) (Kx := fun _ => 0) (Rb := w)
    (S0 := fun _ => 0) (S1 := fun _ => 0) (S2 := fun _ => 0)
    (K := 0) (K2 := 0) (ell := 2 * Real.pi)
    (c0 := 0) (c1 := 0) (c2 := 0) (r := 1 / 2) (kx := 0)
    driftingCircleData.hYC1 driftingCircleData.hY driftingCircleData.hYt
    driftingCircleData.halpha driftingCircleData.hlip driftingCircleData.hcont
    driftingCircleData.hPhid driftingCircleData.hell driftingCircleData.hPhi0
    driftingCircleData.hxd driftingCircleData.hxcont driftingCircleData.hxxd
    driftingCircleData.hxxcont driftingCircleData.hxxK driftingCircleData.hP1
    driftingCircleData.hG1 driftingCircleData.hk driftingCircleData.hC
    driftingCircleData.hC2 driftingCircleData.hCnn driftingCircleData.hC2nn
    driftingCircleData.hcost driftingCircleData.hcost2 driftingCircleData.halphaC1
    driftingCircleData.hkC1 driftingCircleData.halphaT driftingCircleData.hkT
    driftingCircleData.hkX driftingCircleData.halphaTc driftingCircleData.hkTc
    driftingCircleData.hkXc driftingCircleData.hkc driftingCircleData.hKxbd
    driftingCircleData.hRbd driftingCircleData.hKxnn
    (fun t x => hasDerivAt_const x (0 : ℝ)) (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun t s => hasDerivAt_const s (w t))
    mixed_driftingCircle
    (fun t x => by norm_num) (fun t x => by norm_num) (fun t x => by norm_num)
    (fun t => by norm_num) (fun t => by norm_num) (fun t => by norm_num)
    (fun t => by have := w_nonneg t; linarith) (fun t => le_rfl) (by norm_num)
    (fun t => by have := w_nonneg t; linarith) (by norm_num) (by norm_num)
    driftingCircleData.hT driftingCircleData.hencont driftingCircleData.hstart
    driftingCircleData.hfinish driftingCircleData.hmc driftingCircleData.hmstop
    driftingCircleData.hmbd driftingCircleData.hmsup

/-- The angle bound produced by the construction is the one supplied by hand in
`GaugeFlowVariableSpeedPathCircle.driftingCircleData`: `0 + κ̂ · R_b = w`. -/
theorem angleRateBound_driftingCircle (t : ℝ) :
    driftingCircleDataOfNormalRate.A t = w t := by
  show angleRateBound (fun _ => 0) w 1 t = w t
  rw [angleRateBound]
  ring

/-- The curvature bound produced by the construction vanishes, as it does in
`GaugeFlowVariableSpeedPathCircle.driftingCircleData`: the circle keeps its
shape. -/
theorem curvRateBound_driftingCircle (t : ℝ) :
    driftingCircleDataOfNormalRate.Kt t = 0 := by
  show curvRateBound (fun _ => 0) (fun _ => 0) w (fun _ => 0) 1 t = 0
  rw [curvRateBound]
  ring

/-- **The normal path with slices of variable speed produced by the drifting
circle, with its frame-data bounds derived from its normal rate.** -/
theorem exists_variableSpeed_normalPath_driftingCircle_of_normal_rate :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * w t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * w t) ∧
      IsVariableSpeedNormalPath 1 (2 * Real.pi) 1 0 0 Γ :=
  exists_variableSpeed_normalPath_of_data driftingCircleDataOfNormalRate

end GaugeMarkedDataOfNormalRateCircle
