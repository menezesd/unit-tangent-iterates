import Mathlib
import UnitTangentIterates.GaugeFunctionals
import UnitTangentIterates.GlobalODE
import UnitTangentIterates.GlobalODEGrowth

/-!
# The gauge flow of a frame, and its regularity in the parameter

Putting a moving family of curves in normal gauge means transporting the
parameter along the flow of the tangential rate `h = −ξ/v`
(`NormalGaugeFrame.lean`, `NormalGaugeFamily.lean`).  `GaugeRate.lean` shows
that this field satisfies all the hypotheses of `FlowDerivative.lean` as soon
as the frame data are bounded with a speed bounded away from `0`, and
`FlowDerivative.lean` then gives the flow two derivatives in the parameter,
with explicit bounds.

This file assembles the two: the gauge flow of such a frame exists globally, is
a strictly increasing reparametrization of the line for every time, and is
twice differentiable in the parameter with

`ℓe^{−C₁|t|} ≤ ∂_uΦ ≤ ℓe^{C₁|t|}`,  `|∂²_uΦ| ≤ C₂ℓ²|t|e^{2C₁|t|}`,

where `C₁ = A₁/v₀ + A₀B₁/v₀²` and `C₂ = A₂/v₀ + 2A₁B₁/v₀² + A₀(V₁B₂+2B₁²)/v₀³`.
These are exactly the bounds the comparison of the path functionals asks of a
reparametrization (`PathFunctionalsReparam.lean`, `GaugeFunctionals.lean`).

Main result: `exists_gaugeFlow_smooth`.
-/

noncomputable section

open Set Function FlowDerivative GaugeRate

namespace GaugeFlowSmooth

variable {xi xi1 xi2 v v1 v2 : ℝ → ℝ → ℝ} {A0 A1 A2 B1 B2 V1 v0 ell : ℝ}

/-- The tangential rate is bounded by `A₀/v₀`. -/
theorem abs_gaugeRate_le (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (a x : ℝ) : |gaugeRate xi v a x| ≤ A0 / v0 := by
  have hA0' : 0 ≤ A0 := le_trans (abs_nonneg _) (hA0 a x)
  rw [gaugeRate, abs_neg, abs_div]
  gcongr
  · exact hA0 a x
  · exact hvlow a x

/-- **The gauge flow of a frame.**  For frame data with bounded derivatives and
a speed bounded away from `0`, the flow of the tangential rate `−ξ/v` started at
`ℓu` exists globally, is a strictly increasing reparametrization of the line at
each time, and has two derivatives in the parameter, with the two-sided
distortion bound `ℓe^{∓C₁|t|}` for the first and the bound `C₂ℓ²|t|e^{2C₁|t|}`
for the second. -/
theorem exists_gaugeFlow_smooth
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (uncurry xi)) (hxi1c : Continuous (uncurry xi1))
    (hxi2c : Continuous (uncurry xi2)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hv2c : Continuous (uncurry v2))
    (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|) (hvup : ∀ a x, |v a x| ≤ V1)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hA2 : ∀ a x, |xi2 a x| ≤ A2)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (hB2 : ∀ a x, |v2 a x| ≤ B2)
    (hell : 0 < ell) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (gaugeRate xi v t (Phi t u)) t) ∧
      (∀ t, StrictMono (Phi t)) ∧
      (∀ t u, HasDerivAt (fun u' => Phi t u')
        (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u) u) ∧
      (∀ t u, ell * Real.exp (-((A1 / v0 + A0 * B1 / v0 ^ 2) * |t|))
            ≤ flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ∧
          flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u
            ≤ ell * Real.exp ((A1 / v0 + A0 * B1 / v0 ^ 2) * |t|)) ∧
      (∀ t u, HasDerivAt (fun u' => flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u')
          (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u
            * ∫ s in (0:ℝ)..t, gaugeRate2 xi xi1 xi2 v v1 v2 s (Phi s u)
                * flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell s u) u ∧
        |flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u
            * ∫ s in (0:ℝ)..t, gaugeRate2 xi xi1 xi2 v v1 v2 s (Phi s u)
                * flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell s u|
          ≤ (A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3)
              * ell ^ 2 * |t| * Real.exp (2 * (A1 / v0 + A0 * B1 / v0 ^ 2) * |t|)) := by
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    gaugeRate_flow_hypotheses hxi hxi1 hv hv1 hvne hxic hxi1c hxi2c hvc hv1c hv2c
      hv0 hvlow hvup hA0 hA1 hA2 hB1 hB2
  set C1 : ℝ := A1 / v0 + A0 * B1 / v0 ^ 2 with hC1def
  have hC1 : (0:ℝ) ≤ C1 :=
    le_trans (abs_nonneg _) (abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 0 0)
  -- one solution of the gauge equation for each value of the normalized parameter
  have hex : ∀ u : ℝ, ∃ φ : ℝ → ℝ, φ 0 = ell * u ∧
      ∀ t, HasDerivAt φ (gaugeRate xi v t (φ t)) t := fun u =>
    GlobalODE.exists_global_solution_real (h := gaugeRate xi v)
      (K := Real.toNNReal C1) (L := Real.toNNReal (A0 / v0)) hlip
      (fun x => hcont.comp (continuous_id.prodMk continuous_const))
      (fun a x => by
        have hA0' : 0 ≤ A0 := le_trans (abs_nonneg _) (hA0 a x)
        rw [Real.coe_toNNReal _ (by positivity)]
        exact abs_gaugeRate_le hv0 hvlow hA0 a x)
      0 (ell * u)
  choose flow hflow0 hflowd using hex
  set Phi : ℝ → ℝ → ℝ := fun t u => flow u t with hPhidef
  have hPhi0 : ∀ u, Phi 0 u = ell * u := hflow0
  have hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (gaugeRate xi v t (Phi t u)) t :=
    fun u => hflowd u
  -- the derivative in the parameter
  have hderiv : ∀ t u, HasDerivAt (fun u' => Phi t u')
      (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u) u := fun t u =>
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t
  have hbounds : ∀ t u,
      ell * Real.exp (-(C1 * |t|)) ≤ flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ∧
      flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ≤ ell * Real.exp (C1 * |t|) := by
    intro t u
    have := flowDeriv_bounds (K := Real.toNNReal C1) (hx := gaugeRate1 xi xi1 v v1)
      (Phi := Phi) hell (fun s x => by
        rw [Real.coe_toNNReal _ hC1]
        exact abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 s x) t u
    rwa [Real.coe_toNNReal _ hC1] at this
  refine ⟨Phi, hPhi0, hPhid, fun t => ?_, hderiv, hbounds, fun t u => ⟨?_, ?_⟩⟩
  · refine strictMono_of_deriv_pos (fun u => ?_)
    rw [(hderiv t u).deriv]
    exact flowDeriv_pos hell t u
  · exact hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd u t
  · have := abs_flowDeriv_deriv_le (K := Real.toNNReal C1) (hx := gaugeRate1 xi xi1 v v1)
      (hxx := gaugeRate2 xi xi1 xi2 v v1 v2) (Phi := Phi) hell
      (fun s x => by
        rw [Real.coe_toNNReal _ hC1]
        exact abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 s x) hxxbd u t
    rwa [Real.coe_toNNReal _ hC1] at this

/-- **The gauge flow of a frame, from bounds on the rate alone.**  The same
statement as `exists_gaugeFlow_smooth`, with the two distortion constants given
directly as bounds for the two space derivatives of the tangential rate `−ξ/v`.
No bound for `ξ` itself is required, so this version applies to a family of
closed curves whose length changes, whose tangential component drifts by `Q'(t)`
over each arclength period.  Global existence of the flow is
`GlobalODEGrowth.exists_global_solution_real_of_lipschitz`, which needs only the
Lipschitz constant. -/
theorem exists_gaugeFlow_smooth_of_bounds {L K2 : ℝ} (hL : 0 ≤ L)
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (uncurry xi)) (hxi1c : Continuous (uncurry xi1))
    (hxi2c : Continuous (uncurry xi2)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hv2c : Continuous (uncurry v2))
    (hb1 : ∀ a x, |gaugeRate1 xi xi1 v v1 a x| ≤ L)
    (hb2 : ∀ a x, |gaugeRate2 xi xi1 xi2 v v1 v2 a x| ≤ K2)
    (hell : 0 < ell) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (gaugeRate xi v t (Phi t u)) t) ∧
      (∀ t, StrictMono (Phi t)) ∧
      (∀ t u, HasDerivAt (fun u' => Phi t u')
        (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u) u) ∧
      (∀ t u, ell * Real.exp (-(L * |t|))
            ≤ flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ∧
          flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ≤ ell * Real.exp (L * |t|)) ∧
      (∀ t u, HasDerivAt (fun u' => flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u')
          (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u
            * ∫ s in (0:ℝ)..t, gaugeRate2 xi xi1 xi2 v v1 v2 s (Phi s u)
                * flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell s u) u ∧
        |flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u
            * ∫ s in (0:ℝ)..t, gaugeRate2 xi xi1 xi2 v v1 v2 s (Phi s u)
                * flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell s u|
          ≤ K2 * ell ^ 2 * |t| * Real.exp (2 * L * |t|)) := by
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    gaugeRate_flow_hypotheses_of_bounds hL hxi hxi1 hv hv1 hvne hxic hxi1c hxi2c hvc hv1c
      hv2c hb1 hb2
  -- one solution of the gauge equation for each value of the normalized parameter
  have hex : ∀ u : ℝ, ∃ φ : ℝ → ℝ, φ 0 = ell * u ∧
      ∀ t, HasDerivAt φ (gaugeRate xi v t (φ t)) t := fun u =>
    GlobalODEGrowth.exists_global_solution_real_of_lipschitz (h := gaugeRate xi v)
      (K := Real.toNNReal L) hlip
      (fun x => hcont.comp (continuous_id.prodMk continuous_const)) 0 (ell * u)
  choose flow hflow0 hflowd using hex
  set Phi : ℝ → ℝ → ℝ := fun t u => flow u t with hPhidef
  have hPhi0 : ∀ u, Phi 0 u = ell * u := hflow0
  have hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (gaugeRate xi v t (Phi t u)) t :=
    fun u => hflowd u
  have hxbd : ∀ s x, |gaugeRate1 xi xi1 v v1 s x| ≤ ((Real.toNNReal L : NNReal) : ℝ) := by
    intro s x
    rw [Real.coe_toNNReal _ hL]
    exact hb1 s x
  have hderiv : ∀ t u, HasDerivAt (fun u' => Phi t u')
      (flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u) u := fun t u =>
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t
  have hbounds : ∀ t u,
      ell * Real.exp (-(L * |t|)) ≤ flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ∧
      flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell t u ≤ ell * Real.exp (L * |t|) := by
    intro t u
    have := flowDeriv_bounds (K := Real.toNNReal L) (hx := gaugeRate1 xi xi1 v v1)
      (Phi := Phi) hell hxbd t u
    rwa [Real.coe_toNNReal _ hL] at this
  refine ⟨Phi, hPhi0, hPhid, fun t => ?_, hderiv, hbounds, fun t u => ⟨?_, ?_⟩⟩
  · refine strictMono_of_deriv_pos (fun u => ?_)
    rw [(hderiv t u).deriv]
    exact flowDeriv_pos hell t u
  · exact hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd u t
  · have := abs_flowDeriv_deriv_le (K := Real.toNNReal L) (hx := gaugeRate1 xi xi1 v v1)
      (hxx := gaugeRate2 xi xi1 xi2 v v1 v2) (Phi := Phi) hell hxbd hxxbd u t
    rwa [Real.coe_toNNReal _ hL] at this

/-- Non-vacuity: a unit-speed frame whose tangential component is `sin`
satisfies all the hypotheses, so its gauge flow exists with all the stated
properties. -/
example : ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = 1 * u) ∧
    (∀ u t, HasDerivAt (fun r => Phi r u)
      (gaugeRate (fun _ x => Real.sin x) (fun _ _ => 1) t (Phi t u)) t) ∧
    (∀ t, StrictMono (Phi t)) := by
  obtain ⟨Phi, h0, hd, hmono, -⟩ := exists_gaugeFlow_smooth
    (xi := fun _ x => Real.sin x) (xi1 := fun _ x => Real.cos x)
    (xi2 := fun _ x => -Real.sin x) (v := fun _ _ => 1) (v1 := fun _ _ => 0)
    (v2 := fun _ _ => 0) (A0 := 1) (A1 := 1) (A2 := 1) (B1 := 0) (B2 := 0)
    (V1 := 1) (v0 := 1) (ell := 1)
    (fun _ x => Real.hasDerivAt_sin x) (fun _ x => Real.hasDerivAt_cos x)
    (fun _ x => hasDerivAt_const x 1) (fun _ x => hasDerivAt_const x 0)
    (fun _ _ => one_ne_zero)
    (Real.continuous_sin.comp continuous_snd) (Real.continuous_cos.comp continuous_snd)
    ((Real.continuous_sin.comp continuous_snd).neg) continuous_const
    continuous_const continuous_const
    one_pos (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ x => Real.abs_sin_le_one x) (fun _ x => Real.abs_cos_le_one x)
    (fun _ x => by simpa using Real.abs_sin_le_one x)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) one_pos
  exact ⟨Phi, h0, hd, hmono⟩

end GaugeFlowSmooth
