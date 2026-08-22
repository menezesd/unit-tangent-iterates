import Mathlib
import UnitTangentIterates.GaugeGeometryPathVariable
import UnitTangentIterates.GaugeClosingRelations
import UnitTangentIterates.GaugePathDistVariable

/-!
# The normal path of selected rears from the closing relation of the rear family

`GaugeGeometryPathVariable.exists_normalPath_of_gauge_geometry_var` removes the
hypothesis that the rear arclength period is the same at every time, at the
price of two hypotheses on the frame data of the rear family: that the speed is
`Q t`-periodic and that the tangential component of the velocity satisfies
`ξ(t, x + Q t) = ξ(t, x) − Q'(t) v(t, x)`.

For a family written in its **own arclength** — speed `v ≡ 1` — both of them are
consequences of the single geometric fact that the slices close up,
`Y(t, x + Q t) = Y(t, x)`: this is `GaugeClosingRelations.closing_relations`.
This file records the resulting statement, in which the only hypotheses on the
motion of the rear family are geometric ones.

Main results: `exists_normalPath_of_gauge_geometry_closing` and its path-metric
form `pathDist_le_of_gauge_geometry_closing`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugeGeometryPathClosing

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable

/-- **The selected rears of a path of fronts, in the gauge parameter, from the
closing relation of the rear family.**

Same conclusion as
`GaugeGeometryPathVariable.exists_normalPath_of_gauge_geometry_var`, but the two
quasi-periodicity hypotheses on the frame data are replaced by the closing
relation `Y(t, x + Qf t) = Y(t, x)` of the family of rear tracks in arclength
(speed `v ≡ 1`), whose velocity is `ξ τ + η (iτ)` in the frame of the slice. -/
theorem exists_normalPath_of_gauge_geometry_closing {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ} {Y tauY : ℝ → ℝ → ℂ} {etaY : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    -- the front period
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the steering equation on the selected strip
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    -- the front normal velocity
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    -- the change of variable
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    -- the inverse Jacobi ODE for the rear normal velocity
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    -- the rear period, differentiable in the time but not constant
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    -- the front velocity of the given path
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the rear family in its own arclength, and its closing relation
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (Function.uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaY t x : ℂ) * (Complex.I * tauY t x)) t)
    (htau0 : ∀ t x, tauY t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tauY t) (Qf t))
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    -- the gauge flow
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    -- the structural data of the rear family
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst
        (gaugeCW (uarcW P1) D.rateLip Γ.T (Qf 0))
        (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
        (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          D.rateLip Γ.T (Qf 0))
        (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh)
          D.rateLip D.rateBound2 Γ.T (Qf 0))
        * cost Γ := by
  refine exists_normalPath_of_gauge_geometry_var Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper hetaC2 hlink
    (fun t x => by rw [hv1, hv1]) (fun t x => ?_) hPhid hPhi0 hstart hfinish hderiv hcont
    hnu hrest
  have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).1
  rw [hv1, mul_one]
  exact h

/-- **The path pseudodistance of the selected rears, from the closing relation
of the rear family.** -/
theorem pathDist_le_of_gauge_geometry_closing {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ} {Y tauY : ℝ → ℝ → ℂ} {etaY : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (Function.uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaY t x : ℂ) * (Complex.I * tauY t x)) t)
    (htau0 : ∀ t x, tauY t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tauY t) (Qf t))
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0) :
    pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T (Qf 0) * cost Γ := by
  obtain ⟨Δ, -, hcost⟩ := exists_normalPath_of_gauge_geometry_closing Γ D hP0 hkh0 hkh1 hPl
    hPu hsteer hstrip0 hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd
    hetaRper hetaC2 hlink hv1 hY hYx hYt htau0 htauper hclose hPhid hPhi0 hstart hfinish
    hderiv hcont hnu hrest
  calc pathDist p' q' ≤ cost Δ := pathDist_le_cost Δ
    _ = _ := hcost

/-- **The hypotheses are consistent**, on a nondegenerate slice: the constant
path of fronts of curvature `1/2`, with steering angle `arcsin(1/2)`, rear
arclength `x(s) = s·cos(arcsin ½)` and vanishing normal velocities, together
with the family of rear tracks `Y(t, x) = e^{i(2π/Q)x}` — a circle of arclength
period `Q = cos(arcsin ½)`, at rest — satisfies them all: in particular the
closing relation holds, and it is what supplies the two quasi-periodicity
hypotheses. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = jacobiConst
        (gaugeCW (uarcW 1) trivialFrame.rateLip (NormalPath.const p).T
          (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (gaugeC0 (uarc0 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2) * 1)))
        (gaugeC1 (uarc1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2) * 1)
            (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
          trivialFrame.rateLip (NormalPath.const p).T (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (gaugeC2 (uarc1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2) * 1)
            (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
          (uarc2 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2) * 1)
            (Real.sqrt (1 - (1/2 : ℝ) ^ 2)) (1/2))
          trivialFrame.rateLip trivialFrame.rateBound2 (NormalPath.const p).T
          (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        * cost (NormalPath.const p) := by
  set A : ℝ := Real.arcsin (1/2) with hA
  have hsinA : Real.sin A = 1/2 := Real.sin_arcsin (by norm_num) (by norm_num)
  have hcosA : Real.cos A = Real.sqrt (1 - (1/2 : ℝ) ^ 2) := by
    rw [hA, Real.cos_arcsin]
  have hcosApos : 0 < Real.cos A := by
    rw [hcosA]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hArc : rearArclength (fun _ : ℝ => A) = fun y => y * Real.cos A := by
    funext y
    simp [rearArclength]
  have hrate : GaugeRate.gaugeRate trivialFrame.xi trivialFrame.v = fun _ _ => (0:ℝ) := by
    funext t x
    simp [GaugeRate.gaugeRate, trivialFrame]
  set c : ℝ := Real.sqrt (1 - (1/2 : ℝ) ^ 2) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  set a : ℝ := 2 * Real.pi / c with hadef
  have hane : a ≠ 0 := by
    rw [hadef]
    positivity
  have hac : a * c = 2 * Real.pi := by
    rw [hadef]
    field_simp
  have hshift : ∀ x : ℝ, Complex.exp (Complex.I * ((a * (x + c) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)) := by
    intro x
    have h1 : ((a * (x + c) : ℝ) : ℂ) = ((a * x : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast [← hac]
      ring
    rw [h1, mul_add, Complex.exp_add,
      show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one]
  refine exists_normalPath_of_gauge_geometry_closing (p' := p') (q' := p')
    (NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1) (delta := fun _ _ => A)
    (K := fun _ _ => 1/2) (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0)
    (etaR := fun _ _ => 0) (sf := fun _ x => x / Real.cos A)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    (Y := fun _ x => Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)))
    (tauY := fun _ x => Complex.I * (a : ℂ) * Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)))
    (etaY := fun _ _ => 0)
    trivialFrame (Phi := fun _ u => c * u)
    (Qf := fun _ => c) (Qf' := fun _ => 0)
    one_pos (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ s => (hasDerivAt_const s A).congr_deriv (by rw [hsinA]; ring))
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num)
    (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ => continuous_const) (fun _ _ => rfl)
    (fun _ x => by rw [hArc]; field_simp)
    (fun _ x => (hasDerivAt_const x (0:ℝ)).congr_deriv (by simp))
    ?_ (fun t => hasDerivAt_const t _) (fun _ _ => rfl) (fun _ => contDiff_const)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
  · intro t
    rw [hArc]
    simp [hcosA]
  · -- the family of rear tracks is `C¹`
    have h : Function.uncurry (fun (_ x : ℝ) => Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)))
        = fun z : ℝ × ℝ => Complex.exp (Complex.I * ((a * z.2 : ℝ) : ℂ)) := rfl
    rw [h]
    have h1 : ContDiff ℝ (1:ℕ) (fun z : ℝ × ℝ => (a * z.2 : ℝ)) :=
      contDiff_const.mul contDiff_snd
    have h2 : ContDiff ℝ (1:ℕ) (fun z : ℝ × ℝ => ((a * z.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    exact Complex.contDiff_exp.comp (contDiff_const.mul h2)
  · -- its space derivative is the tangent
    intro t x
    have h1 : HasDerivAt (fun y : ℝ => ((a * y : ℝ) : ℂ)) ((a : ℂ)) x := by
      simpa using (((hasDerivAt_id x).const_mul a).ofReal_comp)
    have h2 : HasDerivAt (fun y : ℝ => Complex.I * ((a * y : ℝ) : ℂ))
        (Complex.I * (a : ℂ)) x := h1.const_mul Complex.I
    refine (h2.cexp).congr_deriv ?_
    ring
  · -- it is at rest
    intro t x
    refine (hasDerivAt_const t _).congr_deriv ?_
    simp [trivialFrame]
  · -- the tangent does not vanish
    intro t x
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hane))
      (Complex.exp_ne_zero _)
  · -- the tangent is periodic
    intro t x
    simp only
    rw [hshift x]
  · -- the slices close up
    intro t x
    exact hshift x
  · intro u t
    rw [hrate]
    exact hasDerivAt_const t (c * u)
  · intro t u
    simpa using hasDerivAt_const t (p'.1 u)
  · intro u
    simpa using continuous_const

end GaugeGeometryPathClosing
