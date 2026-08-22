import Mathlib
import UnitTangentIterates.GaugeFlowVariableSpeedPath
import UnitTangentIterates.PathMetricCircle

/-!
# Non-vacuity of the gauge-marked variable-speed path

`GaugeFlowVariableSpeedPath.GaugeMarkedData` packages the data of a family of
curves read in a gauge marking together with the bounds that turn it into a
normal path with slices of variable speed.  This file checks that the whole
block is satisfiable, on a family that really drifts.

The slices are the unit circle, parametrized by its own arclength but with a
phase `B(t)` that runs from `0` to `1` over the time interval, `B` being the
primitive of the bump `w` of `PathMetricCircle.lean`:

```
  Y(t,s) = e^{i(s + B t)} ,   α(t,s) = s + B t + π/2 ,   k ≡ 1 .
```

Its motion is purely tangential, with rate `ξ = w(t)`, so the field of the gauge
flow is `h ≡ −w(t)` and its flow started at the affine marking of period `2π` is

```
  Φ(t,u) = 2π u − B t ,
```

the marking that follows the drift.  Read in it, the family is the fixed
circle, so the path it produces is the constant path at `circleData 1` — but the
cost density `m = 2w` is not identically zero, and neither is the tangential
rate nor the marking: the drift is real and is exactly compensated by the
marking, which is what a gauge marking is for.  (A family whose *shape* moves is
excluded here for a simple reason: the bounds are asked at every time, while the
cost density has to vanish outside the time window, so the family must be at
rest there.)

Main results: `gaugeMarkedData_driftingCircle`, and the resulting normal path
`exists_variableSpeed_normalPath_driftingCircle`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeFlowVariableSpeedPathCircle

open GaugeFlowVariableSpeedPath PathMetricCircle NormalPathC2IncrementVariableSpeed

/-! ### The drifting circle and its gauge marking -/

/-- The drifting unit circle, in its own arclength: the phase `B t` runs from
`0` to `1` over the time interval. -/
def Ydrift (t s : ℝ) : ℂ := Complex.exp (Complex.I * ((s + B t : ℝ) : ℂ))

/-- The tangent angle of the drifting circle. -/
def alphaDrift (t s : ℝ) : ℝ := s + B t + Real.pi / 2

/-- The marking that follows the drift: the flow of the field `−w(t)` started at
the affine marking of period `2π`. -/
def PhiDrift (t u : ℝ) : ℝ := 2 * Real.pi * u - B t

theorem exp_I_pi_div_two : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  have h : Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    ring
  rw [h, Complex.exp_mul_I]
  have h1 : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.cos_pi_div_two
  have h2 : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.sin_pi_div_two
  rw [h1, h2, one_mul, zero_add]

/-- The arclength derivative of the drifting circle is its unit tangent. -/
theorem hasDerivAt_Ydrift_space (t s : ℝ) :
    HasDerivAt (Ydrift t) (Complex.exp (Complex.I * (alphaDrift t s : ℂ))) s := by
  have hlin : HasDerivAt (fun v : ℝ => Complex.I * ((v + B t : ℝ) : ℂ)) Complex.I s := by
    have h0 : HasDerivAt (fun v : ℝ => v + B t) (1 : ℝ) s := (hasDerivAt_id s).add_const (B t)
    have h : HasDerivAt (fun v : ℝ => ((v + B t : ℝ) : ℂ)) (1 : ℂ) s := by
      simpa using h0.ofReal_comp
    simpa using h.const_mul Complex.I
  have h := hlin.cexp
  refine h.congr_deriv ?_
  have hsplit : Complex.exp (Complex.I * (alphaDrift t s : ℂ))
      = Complex.exp (Complex.I * ((s + B t : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, alphaDrift]
    congr 1
    push_cast
    ring
  rw [hsplit, exp_I_pi_div_two]

/-- The drifting circle moves tangentially, at the rate `w(t)`. -/
theorem hasDerivAt_Ydrift_time (t s : ℝ) :
    HasDerivAt (fun r => Ydrift r s)
      (((-(-w t) : ℝ) : ℂ) * Complex.exp (Complex.I * (alphaDrift t s : ℂ))
        + ((0 : ℝ) : ℂ) * (Complex.I * Complex.exp (Complex.I * (alphaDrift t s : ℂ)))) t := by
  have hlin : HasDerivAt (fun r : ℝ => Complex.I * ((s + B r : ℝ) : ℂ))
      (Complex.I * ((w t : ℝ) : ℂ)) t := by
    have h : HasDerivAt (fun r : ℝ => ((s + B r : ℝ) : ℂ)) ((w t : ℂ)) t :=
      ((hasDerivAt_B t).const_add s).ofReal_comp
    exact h.const_mul Complex.I
  have h := hlin.cexp
  refine h.congr_deriv ?_
  have hsplit : Complex.exp (Complex.I * (alphaDrift t s : ℂ))
      = Complex.exp (Complex.I * ((s + B t : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, alphaDrift]
    congr 1
    push_cast
    ring
  rw [hsplit, exp_I_pi_div_two]
  push_cast
  ring

theorem contDiff_B : ContDiff ℝ 1 B := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_B t).differentiableAt, ?_⟩
  have hderiv : deriv B = w := funext fun t => (hasDerivAt_B t).deriv
  rw [hderiv]
  exact continuous_w

theorem contDiff_Ydrift : ContDiff ℝ 1 (uncurry Ydrift) := by
  have hreal : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.2 + B p.1) :=
    contDiff_snd.add (contDiff_B.comp contDiff_fst)
  have hcplx : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * ((p.2 + B p.1 : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hreal)
  exact Complex.contDiff_exp.comp hcplx

theorem contDiff_alphaDrift : ContDiff ℝ 1 (uncurry alphaDrift) :=
  (contDiff_snd.add (contDiff_B.comp contDiff_fst)).add contDiff_const

/-! ### The data -/

/-- **The drifting circle, read in the marking that follows its drift, is a
gauge-marked family with slices of variable speed.**  The whole hypothesis block
of `GaugeFlowVariableSpeedPath.GaugeMarkedData` is satisfied, with a cost
density `m = 2w` that is not identically zero. -/
def driftingCircleData :
    GaugeMarkedData (circleData 1) (circleData 1) 1 (2 * Real.pi) 1 0 0 1
      (fun t => 2 * w t) where
  Y := Ydrift
  alpha := alphaDrift
  k := fun _ _ => 1
  en := fun _ _ => 0
  h := fun t _ => -w t
  hx := fun _ _ => 0
  hxx := fun _ _ => 0
  Phi := PhiDrift
  alphaT := fun t _ => w t
  kT := fun _ _ => 0
  kX := fun _ _ => 0
  C := fun _ => 0
  C2 := fun _ => 0
  A := w
  Kt := fun _ => 0
  Kx := fun _ => 0
  Rb := w
  K := 0
  K2 := 0
  ell := 2 * Real.pi
  hYC1 := contDiff_Ydrift
  hY := hasDerivAt_Ydrift_space
  hYt := hasDerivAt_Ydrift_time
  halpha := fun t s =>
    ((hasDerivAt_id s).add_const (B t)).add_const (Real.pi / 2)
  hlip := fun t => (LipschitzWith.const (-w t)).weaken (by norm_num)
  hcont := by
    have : (uncurry fun (t : ℝ) (_ : ℝ) => -w t) = fun p : ℝ × ℝ => -w p.1 := rfl
    rw [this]
    exact (continuous_w.comp continuous_fst).neg
  hPhid := fun u t => by
    have h : HasDerivAt (fun r : ℝ => 2 * Real.pi * u - B r) (-w t) t := by
      simpa using (hasDerivAt_B t).const_sub (2 * Real.pi * u)
    exact h
  hell := by positivity
  hPhi0 := fun u => by simp [PhiDrift]
  hxd := fun s x => hasDerivAt_const x (-w s)
  hxcont := continuous_const
  hxxd := fun s x => hasDerivAt_const x (0 : ℝ)
  hxxcont := continuous_const
  hxxK := fun s x => by norm_num
  hP1 := fun t u => by
    have h : FlowDerivative.flowDeriv (fun _ _ => (0 : ℝ)) PhiDrift (2 * Real.pi) t u
        = 2 * Real.pi := by
      simp [FlowDerivative.flowDeriv]
    rw [h]
  hG1 := fun t u => by
    simp [GaugeFlowTimeDerivative.flowDeriv2]
  hk := fun t x => by norm_num
  hC := fun t x => by norm_num
  hC2 := fun t x => by norm_num
  hCnn := fun t => le_rfl
  hC2nn := fun t => le_rfl
  hcost := fun t => by
    have := w_nonneg t
    nlinarith [Real.pi_pos]
  hcost2 := fun t => by norm_num
  halphaC1 := contDiff_alphaDrift
  hkC1 := contDiff_const
  halphaT := fun t x => by
    simpa [alphaDrift] using ((hasDerivAt_B t).const_add x).add_const (Real.pi / 2)
  hkT := fun t x => hasDerivAt_const t (1 : ℝ)
  hkX := fun t x => hasDerivAt_const x (1 : ℝ)
  halphaTc := continuous_w.comp continuous_fst
  hkTc := continuous_const
  hkXc := continuous_const
  hkc := continuous_const
  hAbd := fun t x => (abs_of_nonneg (w_nonneg t)).le
  hKtbd := fun t x => by norm_num
  hKxbd := fun t x => by norm_num
  hRbd := fun t x => by rw [abs_neg, abs_of_nonneg (w_nonneg t)]
  hKxnn := fun t => le_rfl
  hcostA := fun t => by
    have := w_nonneg t
    linarith
  hcostK := fun t => by
    have := w_nonneg t
    linarith
  hT := one_pos
  hencont := continuous_const
  hstart := fun u => by
    have h : PhiDrift 0 u = 2 * Real.pi * u := by simp [PhiDrift]
    rw [circleData_fst, normExp, Ydrift, h]
    simp only [B_zero, add_zero]
    push_cast
    ring_nf
  hfinish := fun u => by
    rw [circleData_fst, normExp, Ydrift, PhiDrift]
    push_cast
    ring_nf
  hmc := continuous_const.mul continuous_w
  hm0 := fun t => by have := w_nonneg t; linarith
  hmstop := fun t ht => by rw [w_eq_zero ht]; ring
  hmbd := fun t u => by
    have hw := w_nonneg t
    rw [abs_zero]
    linarith
  hmsup := fun t j _ => by
    have hw := w_nonneg t
    match j with
    | 0 =>
      rw [iteratedDeriv_zero, supNorm_const, abs_zero]
      linarith
    | (n + 1) =>
      rw [iteratedDeriv_succ_const, supNorm_const, abs_zero]
      linarith

/-- The cost density of the drifting circle does not vanish identically: the
data is a genuine gauge-marked family, not a family at rest. -/
theorem cost_density_driftingCircle_ne_zero : 2 * w (1 / 2 : ℝ) ≠ 0 := by
  have h : w (1 / 2 : ℝ) = 3 / 2 := by
    rw [w_eq_of_mem (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- **The normal path with slices of variable speed produced by the drifting
circle**: the hypothesis `Γ'` of the `C²` comparison of the two marked selected
inverses is satisfiable. -/
theorem exists_variableSpeed_normalPath_driftingCircle :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * w t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * w t) ∧
      IsVariableSpeedNormalPath 1 (2 * Real.pi) 1 0 0 Γ :=
  exists_variableSpeed_normalPath_of_data driftingCircleData

end GaugeFlowVariableSpeedPathCircle
