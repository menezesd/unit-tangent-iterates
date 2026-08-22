import Mathlib
import UnitTangentIterates.GaugeJacobiAssemblyVariable
import UnitTangentIterates.SelectedRearArclengthEstimates
import UnitTangentIterates.SelectedInversePathGeometry

/-!
# The normal path of selected rears, from the geometry, with a changing period

`GaugeGeometryPath.exists_normalPath_of_gauge_geometry` produces the normal path
of selected rears in the gauge parameter from the geometry of the slices, but
under one extra hypothesis: that the rear arclength period is the *same* `Q` at
every time of the path — that is, for a family of rears all of the same length.

This file removes that hypothesis.  The rear arclength period
`Q t = ∫₀^{P t} cos δ(t, ·)` of the slice at time `t` is now allowed to vary; all
that is asked of it is that it be differentiable in the time (`hQd`), which is a
regularity property of the family, not a constraint on its geometry.  The gauge
flow then translates by the *current* period at every time
(`GaugeFlowVariablePeriod.flow_translation_var`), so the gauge parameter is
still a normalized parameter, the four densities are still comparable
(`GaugeDensitiesVariable.gauge_densities_le_var`), and the whole chain goes
through with the distortion constants of the reference length `Q 0`.

The hypotheses on the frame data of the rear family are correspondingly the
closing relations of a family whose slices change length: the speed is
`Q t`-periodic and the tangential component of the velocity satisfies
`ξ(t, x + Q t) = ξ(t, x) − Q'(t) v(t, x)`, both obtained by differentiating
`X(t, x + Q t) = X(t, x)` in the time.

Main result: `exists_normalPath_of_gauge_geometry_var`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugeGeometryPathVariable

open UniformFrameBounds GaugeNormalPath GaugeJacobiAssemblyVariable JacobiArclengthUniform
  SelectedInversePathGeometry SelectedRearArclengthEstimates PathMetricJacobi

/-- **The selected rears of a path of fronts, in the gauge parameter, for slices
of changing length.**

Same geometric hypotheses as
`GaugeGeometryPath.exists_normalPath_of_gauge_geometry`, except that the rear
arclength period is no longer assumed constant: it is the function
`Qf t = rearArclength (δ t) (P t)`, assumed only to be differentiable in `t`.
The conclusion is a normal path of rears whose cost is the gauge distortion —
computed with the reference period `Qf 0` — of the uniform arclength constants
times the cost of the front path. -/
theorem exists_normalPath_of_gauge_geometry_var {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ}
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
    -- the gauge flow of the rear family, whose slices change length
    (hvper : ∀ t, Function.Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
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
  set c : ℝ := Real.sqrt (1 - kh ^ 2) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Real.sqrt_pos.mpr (by nlinarith)
  set l : ℝ → ℝ := fun t => rearArclength (delta t) (P t) with hldef
  have hQl : Qf = l := funext hQdef
  subst hQl
  -- basic slice facts
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hdeltac : ∀ t, Continuous (delta t) := fun t =>
    Differentiable.continuous fun s => (hsteer t s).differentiableAt
  have hcos : ∀ t s, c ≤ Real.cos (delta t s) := fun t s =>
    Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)
  have hcospos : ∀ t s, 0 < Real.cos (delta t s) := fun t s =>
    lt_of_lt_of_le hcpos (hcos t s)
  have hcosne : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s => ne_of_gt (hcospos t s)
  have hsin : ∀ t s, |Real.sin (delta t s)| ≤ kh := fun t s =>
    abs_sin_le_of_mem_strip hkh0 hkh1.le (hstrip0 t s) (hstrip1 t s)
  -- the rear arclength and its inverse
  have hxfd : ∀ t s, HasDerivAt (rearArclength (delta t)) (Real.cos (delta t s)) s := fun t s =>
    hasDerivAt_rearArclength (hdeltac t) s
  have hmono : ∀ t, StrictMono (rearArclength (delta t)) := fun t =>
    strictMono_of_deriv_ge hcpos (hxfd t) (hcos t)
  have hsfleft : ∀ t s, sf t (rearArclength (delta t) s) = s := fun t s =>
    leftInverse_of_rightInverse (hmono t).injective (hsfinv t) s
  have hsfc : ∀ t, Continuous (sf t) := fun t =>
    continuous_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t)
  have hsfd : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (delta t (sf t x))) x := fun t x =>
    hasDerivAt_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t) x
  have hsfshift : ∀ t y, sf t (y + l t) = sf t y + P t := fun t y =>
    rightInverse_add_of_shift (hmono t).injective
      (fun s => rearArclength_add_period (hdeltac t) (hdper t) s) (hsfinv t) y
  -- the rear period
  have hlge : ∀ t, c * P0 ≤ l t := by
    intro t
    have h1 : c * P t ≤ l t := rearArclength_ge (hdeltac t) (hcos t) (hPpos t).le
    have h2 : c * P0 ≤ c * P t := by nlinarith [hPl t]
    linarith
  have hlpos : ∀ t, 0 < l t := fun t =>
    lt_of_lt_of_le (mul_pos hcpos hP0) (hlge t)
  -- the steering angle in rear arclength
  set dl : ℝ → ℝ → ℝ := fun t x => delta t (sf t x) with hdldef
  set dxv : ℝ → ℝ → ℝ := fun t x =>
    (K t (sf t x) - Real.sin (delta t (sf t x))) / Real.cos (delta t (sf t x)) with hdxvdef
  have hdld : ∀ t x, HasDerivAt (dl t) (dxv t x) x := by
    intro t x
    have h := (hsteer t (sf t x)).comp x (hsfd t x)
    refine h.congr_deriv ?_
    simp only [hdxvdef]
    field_simp
  -- the transported front velocity
  set G : ℝ → ℝ → ℝ := fun t y => etaF t (sf t y) / Real.cos (dl t y) with hGdef
  have hetaFc : ∀ t, Continuous (etaF t) := fun t =>
    Differentiable.continuous fun s => (hetaFd t s).differentiableAt
  have hGc : ∀ t, Continuous (G t) := by
    intro t
    refine Continuous.div ((hetaFc t).comp (hsfc t)) ?_ ?_
    · exact Real.continuous_cos.comp ((hdeltac t).comp (hsfc t))
    · intro y; exact hcosne t (sf t y)
  have hGper : ∀ t, Function.Periodic (G t) (l t) := by
    intro t y
    simp only [hGdef, hdldef, hsfshift t y]
    rw [hetaFper t (sf t y), hdper t (sf t y)]
  have htransport : ∀ t s, G t (rearArclength (delta t) s) * Real.cos (delta t s) = etaF t s := by
    intro t s
    simp only [hGdef, hdldef, hsfleft t s]
    field_simp [hcosne t s]
  -- boundedness of the velocities
  have hetaFsper : ∀ t, Function.Periodic (etaFs t) (P t) := fun t =>
    periodic_of_hasDerivAt (hetaFd t) (hetaFper t)
  have hFbdd : ∀ t, BddAbove (Set.range fun s => |etaF t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFc t) (hetaFper t)
  have hF1bdd : ∀ t, BddAbove (Set.range fun s => |etaFs t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFsc t) (hetaFsper t)
  -- the four arclength estimates of every slice
  have hraw : ∀ t,
      (∫ x in (0:ℝ)..l t, |etaR t x|) ≤ (∫ s in (0:ℝ)..P t, |etaF t s|)
        ∧ (∀ x, |etaR t x|
            ≤ (1 - Real.exp (-(c * P0)))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
        ∧ (∀ x, |deriv (etaR t) x| ≤ supNorm (etaF t) / c
            + (1 - Real.exp (-(c * P0)))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
        ∧ (∀ x, |deriv (deriv (etaR t)) x|
            ≤ supNorm (etaFs t) / c ^ 2 + 2 * kh ^ 2 * supNorm (etaF t) / c ^ 3
              + (supNorm (etaF t) / c
                + (1 - Real.exp (-(c * P0)))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)) := by
    intro t
    have hres := JacobiAssembly.jacobi_estimates (l := l t) (P := P t) (l0 := c * P0)
      (c := c) (kh := kh) (SF0 := supNorm (etaF t)) (SF1 := supNorm (etaFs t))
      (etaR := etaR t) (etaF := etaF t) (G := G t) (delta := delta t)
      (xf := rearArclength (delta t)) (etaFs := etaFs t) (dl := dl t) (sf := sf t)
      (K := K t) (dxv := dxv t)
      (by positivity) (hlge t) hcpos (hetaFd t)
      (fun s => le_supNorm (hFbdd t) s) (fun s => le_supNorm (hF1bdd t) s) (hK t)
      (hdeltac t) (hcospos t) (fun x => hcos t (sf t x)) (fun x => hsin t (sf t x))
      (hsfd t) (hdld t) (fun _ => rfl) (hxfd t) (by simp [rearArclength]) rfl rfl
      (hGc t) (hGper t) (fun x => hetaR t x)
      (hetaRper t) (htransport t)
    exact hres
  -- the front slice of the path, in arclength and normalized
  have hGamma : ∀ t, Γ.eta t = fun u => etaF t (P t * u) := fun t => funext (hlink t)
  have hn0 : ∀ t, supNorm (etaF t) ≤ supNorm (Γ.eta t) := by
    intro t
    rw [hGamma t]
    exact le_of_eq (JacobiNormalized.supNorm_comp_mul (ne_of_gt (hPpos t)) (etaF t)).symm
  have hn1 : ∀ t, P t * supNorm (etaFs t) ≤ supNorm (iteratedDeriv 1 (Γ.eta t)) := by
    intro t
    rw [hGamma t, JacobiNormalized.iteratedDeriv_one_comp_mul (hetaFd t),
      JacobiNormalized.supNorm_const_mul (hPpos t).le,
      JacobiNormalized.supNorm_comp_mul (ne_of_gt (hPpos t)) (etaFs t)]
  -- feed them into the gauge assembly
  exact GaugeJacobiAssemblyVariable.exists_normalPath_of_arclength_jacobi_var Γ D
    hlpos hQd hvper hxiqp hPhid hPhi0
    hetaC2 hetaRper hstart hfinish hderiv hcont hnu hrest
    (P := P) (P0 := P0) (P1 := P1) (l0 := c * P0) (c := c) (kh := kh)
    (SF0 := fun t => supNorm (etaF t)) (SF1 := fun t => supNorm (etaFs t))
    (etaF := etaF) (etaR1 := fun t => deriv (etaR t))
    (etaR2 := fun t => deriv (deriv (etaR t)))
    hP0 (lt_of_lt_of_le hP0 ((hPl 0).trans (hPu 0))) (by positivity) hcpos hPl hPu hlink
    (fun t x => by
      have h : HasDerivAt (etaR t) (deriv (etaR t) x) x := by
        rw [(hetaR t x).deriv]; exact hetaR t x
      exact h)
    (fun t x => by
      have hcos0 : Real.cos (dl t x) ≠ 0 := ne_of_gt (lt_of_lt_of_le hcpos (hcos t (sf t x)))
      have h := JacobiAssembly.etaR_second_hasDerivAt (etaR := etaR t) (etaF := etaF t)
        (G := G t) (dl := dl t) (sf := sf t) (etaFs := etaFs t (sf t x)) (dxv := dxv t x)
        (fun y => hetaR t y) rfl hcos0 (hsfd t x) (hdld t x) (hetaFd t (sf t x))
      have h2 : HasDerivAt (deriv (etaR t)) (deriv (deriv (etaR t)) x) x := by
        rw [h.deriv]; exact h
      exact h2)
    (fun t => supNorm_nonneg _)
    (fun t _ => (hraw t).1) (fun t _ => (hraw t).2.1) (fun t _ => (hraw t).2.2.1)
    (fun t _ => (hraw t).2.2.2) (fun t _ => hn0 t) (fun t _ => hn1 t)

/-- **The hypotheses are consistent**, on a nondegenerate slice: the constant
path of fronts of curvature `1/2`, with steering angle `arcsin(1/2)`, rear
arclength `x(s) = s·cos(arcsin ½)`, vanishing normal velocities and the trivial
frame data satisfies them all — now with the rear period supplied as a function
of the time (here the constant function, whose derivative vanishes; a genuinely
changing period is exhibited for the flow itself in
`GaugeFlowVariablePeriod`). -/
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
  refine exists_normalPath_of_gauge_geometry_var (p' := p') (q' := p') (NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1) (delta := fun _ _ => A)
    (K := fun _ _ => 1/2) (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0)
    (etaR := fun _ _ => 0) (sf := fun _ x => x / Real.cos A)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    trivialFrame (Phi := fun _ u => Real.sqrt (1 - (1/2 : ℝ) ^ 2) * u)
    (Qf := fun _ => Real.sqrt (1 - (1/2 : ℝ) ^ 2)) (Qf' := fun _ => 0)
    one_pos (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ s => (hasDerivAt_const s A).congr_deriv (by rw [hsinA]; ring))
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num)
    (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ => continuous_const) (fun _ _ => rfl)
    (fun _ x => by rw [hArc]; field_simp)
    (fun _ x => (hasDerivAt_const x (0:ℝ)).congr_deriv (by simp))
    ?_ (fun t => hasDerivAt_const t _) (fun _ _ => rfl) (fun _ => contDiff_const)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by simp [trivialFrame])
    ?_ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
  · intro t
    rw [hArc, ← hcosA]
    ring
  · intro u t
    rw [hrate]
    exact hasDerivAt_const t (Real.sqrt (1 - (1/2 : ℝ) ^ 2) * u)
  · intro t u
    simpa using hasDerivAt_const t (p'.1 u)
  · intro u
    simpa using continuous_const


end GaugeGeometryPathVariable
