import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfTangential
import UnitTangentIterates.GaugeFlowVariableSpeedPathCircle

/-!
# Non-vacuity of the tangential form of the construction

`GaugeMarkedDataOfTangential.exists_variableSpeed_normalPath_of_tangential`
produces the comparison path of the `C²` estimate from the tangential component
`ξ` of the motion alone, the marking being the flow of `−ξ`.  Since the bundle
of frame data it builds on asks for a jointly `C³` tangential component, the
drifting circle of `GaugeFlowVariableSpeedPathCircle.lean` — whose drift is the
merely continuous bump `w` — is not admissible here.  This file replaces that
bump by a smooth one, built from `Real.smoothTransition`, and checks the whole
hypothesis block on the resulting drifting circle:

```
  ξ(t,x) = ws t ,  Y(t,s) = e^{i(s + Bs t)} ,  α(t,s) = s + Bs t + π/2 ,  k ≡ 1 ,
```

with `Bs` the primitive of `ws`.  The motion is purely tangential, so the normal
rate vanishes and the inverse Jacobi ODE holds with zero inhomogeneity; the
marking the theorem produces is the drift marking `Φ(t,u) = 2π u − Bs t`, which
is not the affine one, and the cost density `m = 2·ws` is not identically zero.

Main results: `ws`, `exists_variableSpeed_normalPath_smoothDrift_of_tangential`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfTangentialCircle

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfTangential
  MarkedTopology NormalPathC2IncrementVariableSpeed PathMetricCircle UniformFrameBounds

/-! ### A smooth bump supported in the unit interval -/

/-- A smooth bump, positive exactly on `(0,1)`. -/
def ws (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t) * Real.smoothTransition (2 - 2 * t)

theorem ws_nonneg (t : ℝ) : 0 ≤ ws t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem contDiff_ws {n : ℕ∞} : ContDiff ℝ n ws := by
  have h1 : ContDiff ℝ n fun t : ℝ => 2 * t := contDiff_const.mul contDiff_id
  have h2 : ContDiff ℝ n fun t : ℝ => 2 - 2 * t := contDiff_const.sub h1
  exact (Real.smoothTransition.contDiff.comp h1).mul
    (Real.smoothTransition.contDiff.comp h2)

theorem continuous_ws : Continuous ws := (contDiff_ws (n := 1)).continuous

theorem ws_eq_zero {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : ws t = 0 := by
  by_cases h : t ≤ 0
  · rw [ws, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · push_neg at h
    have h1 : (1 : ℝ) ≤ t := by
      by_contra hlt
      exact ht ⟨h, by linarith [not_le.mp hlt]⟩
    rw [ws, Real.smoothTransition.zero_of_nonpos (x := 2 - 2 * t) (by linarith),
      mul_zero]

/-- The bump is not identically zero. -/
theorem ws_half : ws (1 / 2 : ℝ) = 1 := by
  rw [ws, Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.one_of_one_le (by norm_num), one_mul]

/-- The primitive of the bump. -/
def Bs (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..t, ws x

theorem hasDerivAt_Bs (t : ℝ) : HasDerivAt Bs (ws t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_ws.intervalIntegrable 0 t)
    (continuous_ws.stronglyMeasurableAtFilter _ _) continuous_ws.continuousAt

@[simp] theorem Bs_zero : Bs 0 = 0 := by simp [Bs]

theorem contDiff_Bs : ContDiff ℝ 1 Bs := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_Bs t).differentiableAt, ?_⟩
  have hderiv : deriv Bs = ws := funext fun t => (hasDerivAt_Bs t).deriv
  rw [hderiv]
  exact continuous_ws

/-! ### The smoothly drifting circle -/

/-- The smoothly drifting unit circle, in its own arclength. -/
def Ysm (t s : ℝ) : ℂ := Complex.exp (Complex.I * ((s + Bs t : ℝ) : ℂ))

/-- Its tangent angle. -/
def alphaSm (t s : ℝ) : ℝ := s + Bs t + Real.pi / 2

/-- Its tangential component: the bump, constant in the arclength. -/
def xiSm (t : ℝ) (_ : ℝ) : ℝ := ws t

theorem hasDerivAt_Ysm_space (t s : ℝ) :
    HasDerivAt (Ysm t) (Complex.exp (Complex.I * (alphaSm t s : ℂ))) s := by
  have hlin : HasDerivAt (fun v : ℝ => Complex.I * ((v + Bs t : ℝ) : ℂ)) Complex.I s := by
    have h0 : HasDerivAt (fun v : ℝ => v + Bs t) (1 : ℝ) s := (hasDerivAt_id s).add_const (Bs t)
    have h : HasDerivAt (fun v : ℝ => ((v + Bs t : ℝ) : ℂ)) (1 : ℂ) s := by
      simpa using h0.ofReal_comp
    simpa using h.const_mul Complex.I
  have h := hlin.cexp
  refine h.congr_deriv ?_
  have hsplit : Complex.exp (Complex.I * (alphaSm t s : ℂ))
      = Complex.exp (Complex.I * ((s + Bs t : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, alphaSm]
    congr 1
    push_cast
    ring
  rw [hsplit, GaugeFlowVariableSpeedPathCircle.exp_I_pi_div_two]

theorem hasDerivAt_Ysm_time (t s : ℝ) :
    HasDerivAt (fun r => Ysm r s)
      ((xiSm t s : ℂ) * Complex.exp (Complex.I * (alphaSm t s : ℂ))
        + ((0 : ℝ) : ℂ) * (Complex.I * Complex.exp (Complex.I * (alphaSm t s : ℂ)))) t := by
  have hlin : HasDerivAt (fun r : ℝ => Complex.I * ((s + Bs r : ℝ) : ℂ))
      (Complex.I * ((ws t : ℝ) : ℂ)) t := by
    have h : HasDerivAt (fun r : ℝ => ((s + Bs r : ℝ) : ℂ)) ((ws t : ℂ)) t :=
      ((hasDerivAt_Bs t).const_add s).ofReal_comp
    exact h.const_mul Complex.I
  have h := hlin.cexp
  refine h.congr_deriv ?_
  have hsplit : Complex.exp (Complex.I * (alphaSm t s : ℂ))
      = Complex.exp (Complex.I * ((s + Bs t : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, alphaSm]
    congr 1
    push_cast
    ring
  rw [hsplit, GaugeFlowVariableSpeedPathCircle.exp_I_pi_div_two, xiSm]
  push_cast
  ring

theorem contDiff_Ysm : ContDiff ℝ 1 (uncurry Ysm) := by
  have hreal : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.2 + Bs p.1) :=
    contDiff_snd.add (contDiff_Bs.comp contDiff_fst)
  have hcplx : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * ((p.2 + Bs p.1 : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hreal)
  exact Complex.contDiff_exp.comp hcplx

theorem contDiff_alphaSm : ContDiff ℝ 1 (uncurry alphaSm) :=
  (contDiff_snd.add (contDiff_Bs.comp contDiff_fst)).add contDiff_const

theorem contDiff_xiSm : ContDiff ℝ (3 : ℕ) (uncurry xiSm) := by
  have h : ContDiff ℝ (3 : ℕ) ws := contDiff_ws
  exact h.comp contDiff_fst

/-- The tangential component is constant in the arclength, so its arclength
derivative vanishes. -/
theorem partialX_xiSm (t x : ℝ) : partialX xiSm t x = 0 := by
  have h1 : ContDiff ℝ (1 : ℕ) (uncurry xiSm) :=
    contDiff_xiSm.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3))
  have hd : HasDerivAt (xiSm t) (partialX xiSm t x) x := hasDerivAt_partialX h1 t x
  exact hd.unique (hasDerivAt_const x (ws t))

theorem partialX_partialX_xiSm (t x : ℝ) : partialX (partialX xiSm) t x = 0 := by
  have h1 : ContDiff ℝ (1 : ℕ) (uncurry (partialX xiSm)) := by
    have h2 : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xiSm) := by
      exact_mod_cast contDiff_xiSm.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3))
    exact contDiff_partialX h2
  have hd : HasDerivAt (partialX xiSm t) (partialX (partialX xiSm) t x) x :=
    hasDerivAt_partialX h1 t x
  have hconst : partialX xiSm t = fun _ => (0 : ℝ) := funext fun y => partialX_xiSm t y
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const x (0 : ℝ))

/-- The mixed second derivative of the velocity of the smoothly drifting
circle. -/
theorem mixed_smoothDrift (t s : ℝ) : ∃ W : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (alphaSm r s : ℂ))) W t ∧
    HasDerivAt (fun x => (xiSm t x : ℂ) * Complex.exp (Complex.I * (alphaSm t x : ℂ))
      + ((0 : ℝ) : ℂ) * (Complex.I * Complex.exp (Complex.I * (alphaSm t x : ℂ)))) W s := by
  refine ⟨Complex.I * ((ws t : ℝ) : ℂ) * Complex.exp (Complex.I * (alphaSm t s : ℂ)), ?_, ?_⟩
  · have halphaT : HasDerivAt (fun r : ℝ => alphaSm r s) (ws t) t := by
      simpa [alphaSm] using ((hasDerivAt_Bs t).const_add s).add_const (Real.pi / 2)
    have h1 : HasDerivAt (fun r : ℝ => Complex.I * ((alphaSm r s : ℝ) : ℂ))
        (Complex.I * ((ws t : ℝ) : ℂ)) t := halphaT.ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  · have halphaS : ∀ x : ℝ, HasDerivAt (alphaSm t) (1 : ℝ) x := fun x =>
      ((hasDerivAt_id x).add_const (Bs t)).add_const (Real.pi / 2)
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * ((alphaSm t x : ℝ) : ℂ))
        (Complex.I * ((1 : ℝ) : ℂ)) s := (halphaS s).ofReal_comp.const_mul Complex.I
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (alphaSm t x : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (alphaSm t s : ℂ))) s := by
      simpa [mul_comm, mul_assoc] using h1.cexp
    have h3 := (h2.const_mul ((ws t : ℝ) : ℂ)).add
      ((h2.const_mul Complex.I).const_mul (((0 : ℝ) : ℂ)))
    refine h3.congr_deriv ?_
    push_cast [xiSm]
    ring

/-- The marking the theorem produces is the drift marking. -/
theorem flow_eq_drift {Phi : ℝ → ℝ → ℝ} (hPhi0 : ∀ u, Phi 0 u = 2 * Real.pi * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (-xiSm t (Phi t u)) t) (t u : ℝ) :
    Phi t u = 2 * Real.pi * u - Bs t := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r' => Phi r' u - (2 * Real.pi * u - Bs r')) 0 r := by
    intro r
    have h1 : HasDerivAt (fun r' => Phi r' u) (-ws r) r := by simpa [xiSm] using hPhid u r
    have h2 : HasDerivAt (fun r' => 2 * Real.pi * u - Bs r') (-ws r) r := by
      simpa [sub_eq_add_neg] using (hasDerivAt_Bs r).const_sub (2 * Real.pi * u)
    simpa using h1.sub h2
  have hconst : ∀ r : ℝ, Phi r u - (2 * Real.pi * u - Bs r) = Phi 0 u - (2 * Real.pi * u - Bs 0) :=
    fun r => is_const_of_deriv_eq_zero (fun r' => (hd r').differentiableAt)
      (fun r' => (hd r').deriv) r 0
  have h0 : Phi 0 u - (2 * Real.pi * u - Bs 0) = 0 := by rw [hPhi0 u, Bs_zero]; ring
  have := hconst t
  rw [h0] at this
  linarith [this]

/-! ### The instance -/

/-- **The smoothly drifting circle satisfies the tangential form of the
hypothesis block**, and hence produces the normal path with slices of variable
speed, with its marking produced from the tangential component of the motion
alone. -/
theorem exists_variableSpeed_normalPath_smoothDrift_of_tangential :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * ws t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * ws t) ∧
      IsVariableSpeedNormalPath 1
        (costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * ws t)) 1
        (costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * ws t))
        (1 * costG1 (2 * Real.pi) 1 0 (∫ t in (0 : ℝ)..1, 2 * ws t)
          + 0 * costP1 (2 * Real.pi) 1 (∫ t in (0 : ℝ)..1, 2 * ws t) ^ 2) Γ := by
  obtain ⟨Phi, hPhi0, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_tangential (Y := Ysm) (alpha := alphaSm)
      (k := fun _ _ => 1) (en := fun _ _ => 0) (enS := fun _ _ => 0) (enSS := fun _ _ => 0)
      (g := fun _ _ => 0) (gS := fun _ _ => 0) (alphaT := fun t _ => ws t)
      (kT := fun _ _ => 0) (kX := fun _ _ => 0) (xi := xiSm) (C := fun _ => 0)
      (C2 := fun _ => 0) (Kx := fun _ => 0) (Rb := ws) (S0 := fun _ => 0)
      (Dd := fun _ => 0) (m := fun t => 2 * ws t) (ell := 2 * Real.pi) (T := 1)
      (P0 := 1) (khat := 1) (kappa2 := 0) (c := 0) (d := 0) (r := 1 / 2) (kx := 0)
      contDiff_xiSm (by positivity) contDiff_Ysm hasDerivAt_Ysm_space hasDerivAt_Ysm_time
      (fun t s => ((hasDerivAt_id s).add_const (Bs t)).add_const (Real.pi / 2))
      (fun t x => by norm_num) le_rfl
      (fun t x => by rw [partialX_xiSm t x, abs_zero])
      (fun t x => by rw [partialX_partialX_xiSm t x, abs_zero])
      continuous_const continuous_const
      (fun t => by have := ws_nonneg t; simp only [one_mul]; linarith) (fun t => by norm_num)
      contDiff_alphaSm contDiff_const
      (fun t x => by
        simpa [alphaSm] using (((hasDerivAt_Bs t).const_add x).add_const (Real.pi / 2)))
      (fun t x => hasDerivAt_const t (1 : ℝ)) (fun t x => hasDerivAt_const x (1 : ℝ))
      (continuous_ws.comp continuous_fst) continuous_const continuous_const continuous_const
      (fun t x => by norm_num) (fun t x => by rw [xiSm, abs_of_nonneg (ws_nonneg t)])
      (fun t => le_rfl)
      (fun t x => hasDerivAt_const x (0 : ℝ)) (fun t x => hasDerivAt_const x (0 : ℝ))
      (fun t s => hasDerivAt_const s (ws t)) mixed_smoothDrift
      (fun t x => hasDerivAt_const x (0 : ℝ))
      (fun t x => by simpa using hasDerivAt_const x (0 : ℝ))
      (fun t x => by norm_num) (fun t x => by norm_num) (fun t x => by norm_num)
      (fun t => by norm_num) (fun t => by norm_num)
      (fun t => by have := ws_nonneg t; linarith) (fun t => le_rfl) (by norm_num)
      (fun t => by have := ws_nonneg t; linarith) (by norm_num) (by norm_num)
      one_pos continuous_const (continuous_const.mul continuous_ws)
      (fun t ht => by show 2 * ws t = 0; rw [ws_eq_zero ht, mul_zero])
  have hPhieq : ∀ t u, Phi t u = 2 * Real.pi * u - Bs t := flow_eq_drift hPhi0 hPhid
  refine hmain (circleData 1) (circleData 1) ?_ ?_ ?_ ?_
  · intro u
    rw [hPhieq 0 u, circleData_fst, normExp, Ysm, Bs_zero]
    push_cast
    ring_nf
  · intro u
    rw [hPhieq 1 u, circleData_fst, normExp, Ysm]
    push_cast
    ring_nf
  · intro t u
    have := ws_nonneg t
    rw [abs_zero]
    linarith
  · intro t j hj
    have hw := ws_nonneg t
    match j with
    | 0 =>
      rw [iteratedDeriv_zero, supNorm_const, abs_zero]
      linarith
    | (n + 1) =>
      rw [iteratedDeriv_succ_const, supNorm_const, abs_zero]
      linarith

/-- The cost density of the smoothly drifting circle does not vanish
identically: the marking really moves. -/
theorem cost_density_smoothDrift_ne_zero : 2 * ws (1 / 2 : ℝ) ≠ 0 := by
  rw [ws_half]
  norm_num

end GaugeMarkedDataOfTangentialCircle
