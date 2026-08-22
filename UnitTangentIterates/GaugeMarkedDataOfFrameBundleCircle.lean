import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfFrameBundle
import UnitTangentIterates.GaugeMarkedDataOfNormalRateCircle

/-!
# Non-vacuity of the frame-bundle form of the construction

`GaugeMarkedDataOfFrameBundle.exists_variableSpeed_normalPath_of_frameBundle`
produces the comparison path of the `C²` estimate from a bundle of frame data,
the marking being the gauge flow of the tangential rate of the bundle rather
than a datum.  This file checks that its hypothesis block is satisfiable, on the
drifting circle of `GaugeFlowVariableSpeedPathCircle.lean`: the tangential
component of its motion is the bump `w(t)`, constant in the arclength, and the
speed of its slices is one, so it *is* a bundle of frame data, with both rate
bounds zero.  The marking the theorem produces is then the drift marking
`Φ(t,u) = 2π u − B t` itself, since a flow line of a space-independent field is
determined by integrating the field.

Main results: `driftFrameData`,
`exists_variableSpeed_normalPath_driftingCircle_of_frameBundle`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfFrameBundleCircle

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeFlowVariableSpeedPathCircle
  GaugeMarkedDataOfFrameBundle GaugeMarkedDataOfNormalRateCircle
  NormalPathC2IncrementVariableSpeed PathMetricCircle UniformFrameBounds

/-- **The bundle of frame data of the drifting circle**: the tangential
component of the motion is `w(t)`, constant in the arclength, and the slices
have unit speed, so both bounds on the tangential rate vanish. -/
def driftFrameData : GaugeFrameData where
  xi := fun t _ => w t
  xi1 := fun _ _ => 0
  xi2 := fun _ _ => 0
  v := fun _ _ => 1
  v1 := fun _ _ => 0
  v2 := fun _ _ => 0
  rateLip := 0
  rateBound2 := 0
  hxi := fun t x => hasDerivAt_const x (w t)
  hxi1 := fun _ x => hasDerivAt_const x (0 : ℝ)
  hv := fun _ x => hasDerivAt_const x (1 : ℝ)
  hv1 := fun _ x => hasDerivAt_const x (0 : ℝ)
  hvne := fun _ _ => one_ne_zero
  hxic := continuous_w.comp continuous_fst
  hxi1c := continuous_const
  hxi2c := continuous_const
  hvc := continuous_const
  hv1c := continuous_const
  hv2c := continuous_const
  hrate1 := fun _ _ => by simp [GaugeRate.gaugeRate1]
  hrate2 := fun _ _ => by simp [GaugeRate.gaugeRate2]

/-- The tangential rate of the bundle is the field of the drift marking. -/
theorem gaugeRate_driftFrameData (t x : ℝ) :
    GaugeRate.gaugeRate driftFrameData.xi driftFrameData.v t x = -w t := by
  simp [GaugeRate.gaugeRate, driftFrameData]

/-- A flow line of the space-independent field `−w` started at the affine
marking of period `2π` is the drift marking. -/
theorem flow_eq_PhiDrift {Phi : ℝ → ℝ → ℝ} (hPhi0 : ∀ u, Phi 0 u = 2 * Real.pi * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate driftFrameData.xi driftFrameData.v t (Phi t u)) t) (t u : ℝ) :
    Phi t u = PhiDrift t u := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r' => Phi r' u - PhiDrift r' u) 0 r := by
    intro r
    have h1 : HasDerivAt (fun r' => Phi r' u) (-w r) r := by
      simpa [gaugeRate_driftFrameData] using hPhid u r
    have h2 : HasDerivAt (fun r' => PhiDrift r' u) (-w r) r := by
      have := (hasDerivAt_B r).const_sub (2 * Real.pi * u)
      simpa [PhiDrift, sub_eq_add_neg] using this
    simpa using h1.sub h2
  have hconst : ∀ r : ℝ, Phi r u - PhiDrift r u = Phi 0 u - PhiDrift 0 u := by
    intro r
    have hdiff : Differentiable ℝ fun r' => Phi r' u - PhiDrift r' u := fun r' =>
      (hd r').differentiableAt
    have hzero : ∀ r' : ℝ, deriv (fun r'' => Phi r'' u - PhiDrift r'' u) r' = 0 :=
      fun r' => (hd r').deriv
    exact is_const_of_deriv_eq_zero hdiff hzero r 0
  have h0 : Phi 0 u - PhiDrift 0 u = 0 := by
    rw [hPhi0 u, PhiDrift]
    simp
  have := hconst t
  rw [h0] at this
  linarith [this]

/-- **The drifting circle satisfies the frame-bundle form of the hypothesis
block**, and hence produces the normal path with slices of variable speed, with
its marking produced by the bundle rather than assumed. -/
theorem exists_variableSpeed_normalPath_driftingCircle_of_frameBundle :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * w t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * w t) ∧
      IsVariableSpeedNormalPath 1
        (costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * w t)) 1
        (costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * w t))
        (1 * costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * w t)
          + 0 * costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * w t) ^ 2) Γ := by
  obtain ⟨Phi, hPhi0, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_frameBundle (Y := Ydrift) (alpha := alphaDrift)
      (k := fun _ _ => 1) (en := fun _ _ => 0) (enS := fun _ _ => 0) (enSS := fun _ _ => 0)
      (g := fun _ _ => 0) (gS := fun _ _ => 0) (alphaT := fun t _ => w t)
      (kT := fun _ _ => 0) (kX := fun _ _ => 0) (C := fun _ => 0) (C2 := fun _ => 0)
      (Kx := fun _ => 0) (Rb := w) (S0 := fun _ => 0) (Dd := fun _ => 0)
      (m := fun t => 2 * w t) (ell := 2 * Real.pi) (T := 1) (P0 := 1) (khat := 1)
      (kappa2 := 0) (c := 0) (d := 0) (r := 1 / 2) (kx := 0)
      driftFrameData (fun _ _ => rfl) (by positivity)
      contDiff_Ydrift hasDerivAt_Ydrift_space
      (fun t s => by simpa only [neg_neg] using hasDerivAt_Ydrift_time t s)
      driftingCircleData.halpha driftingCircleData.hk le_rfl
      (fun t x => by simp [GaugeRate.gaugeRate1, driftFrameData])
      (fun t x => by simp [GaugeRate.gaugeRate2, driftFrameData])
      continuous_const continuous_const
      (fun t => by have := w_nonneg t; simp only [one_mul]; linarith) (fun t => by norm_num)
      contDiff_alphaDrift driftingCircleData.hkC1 driftingCircleData.halphaT
      driftingCircleData.hkT driftingCircleData.hkX driftingCircleData.halphaTc
      driftingCircleData.hkTc driftingCircleData.hkXc driftingCircleData.hkc
      driftingCircleData.hKxbd (fun t x => (abs_of_nonneg (w_nonneg t)).le)
      driftingCircleData.hKxnn
      (fun t x => hasDerivAt_const x (0 : ℝ)) (fun t x => hasDerivAt_const x (0 : ℝ))
      (fun t s => hasDerivAt_const s (w t))
      (fun t s => by
        obtain ⟨W, hW1, hW2⟩ := mixed_driftingCircle t s
        exact ⟨W, hW1, by simpa only [neg_neg] using hW2⟩)
      (fun t x => hasDerivAt_const x (0 : ℝ))
      (fun t x => by simpa using hasDerivAt_const x (0 : ℝ))
      (fun t x => by norm_num) (fun t x => by norm_num) (fun t x => by norm_num)
      (fun t => by norm_num) (fun t => by norm_num)
      (fun t => by have := w_nonneg t; linarith) (fun t => le_rfl) (by norm_num)
      (fun t => by have := w_nonneg t; linarith) (by norm_num) (by norm_num)
      driftingCircleData.hT driftingCircleData.hencont driftingCircleData.hmc
      driftingCircleData.hmstop
  have hPhieq : ∀ t u, Phi t u = PhiDrift t u := flow_eq_PhiDrift hPhi0 hPhid
  refine hmain (circleData 1) (circleData 1) ?_ ?_ ?_ ?_
  · intro u
    rw [hPhieq 0 u]
    exact driftingCircleData.hstart u
  · intro u
    rw [hPhieq 1 u]
    exact driftingCircleData.hfinish u
  · intro t u
    have := w_nonneg t
    simp only [abs_zero]
    linarith
  · intro t j hj
    have h := driftingCircleData.hmsup t j hj
    simpa only [hPhieq] using h

end GaugeMarkedDataOfFrameBundleCircle
