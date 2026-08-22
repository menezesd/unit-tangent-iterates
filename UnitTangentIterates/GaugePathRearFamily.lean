import Mathlib
import UnitTangentIterates.GaugeGeometryPathFront
import UnitTangentIterates.GaugeFlowSmooth
import UnitTangentIterates.MarkedSpaceCircle
import UnitTangentIterates.RearPeriodDeriv
import UnitTangentIterates.GaugeBaseFlow

/-!
# The normal path of selected rears, read off the family of rear tracks

`GaugeGeometryPathFront.pathDist_le_of_gauge_geometry_front` still takes as data
the gauge flow `Φ`, the moving marked curve `X_R` and its unit normal `ν_R`,
together with several compatibility hypotheses.  All of them are determined by
the family of rear tracks `Y` itself:

* the gauge flow exists, by `GaugeFlowSmooth.exists_gaugeFlow_smooth`, as soon
  as the frame data of the family are bounded (that is exactly what a
  `GaugeFrameData` bundles), and it starts from the rescaled arclength;
* the moving marked curve is the family read in that parameter,
  `X_R(t, u) = Y(t, Φ(t, u))`, and its velocity is computed by the chain rule:
  the tangential part of the motion is cancelled by the sliding of the gauge
  parameter, so that `∂_t X_R = η_R · iτ` is normal, as a normal path requires;
* the unit normal is `iτ`, of modulus one because the slices are written in
  their arclength;
* the periodicity of the tangent and of the normal velocity in the rear period
  are consequences of the closing relation (`GaugeClosingRelations`).

Main results: `hasDerivAt_along_curve` (the chain rule along a moving point),
and `pathDist_le_of_rear_family`, where the only hypotheses left on the rear
side are that the family is `C¹`, written in its own arclength, closing up with
period `Q t`, and moving with normal component the solution of the inverse
Jacobi ODE.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugePathRearFamily

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable GaugeGeometryPathFront

/-! ### Differentiating along a moving point -/

/-- **The chain rule along a moving point.**  For a `C¹` family `Y` with
partial derivatives `∂_x Y = τ` and `∂_t Y = Y_t`, the value of the family at a
moving point `φ(t)` moves with velocity `Y_t + φ'·τ`. -/
theorem hasDerivAt_along_curve {Y Yt tauY : ℝ → ℝ → ℂ} {phi : ℝ → ℝ} {t phi' : ℝ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x) (Yt t x) t)
    (hphi : HasDerivAt phi phi' t) :
    HasDerivAt (fun r => Y r (phi r)) (Yt t (phi t) + phi' • tauY t (phi t)) t := by
  have hdiff : DifferentiableAt ℝ (uncurry Y) (t, phi t) :=
    (hY.differentiable (by norm_num)) _
  have hL := hdiff.hasFDerivAt
  set L := fderiv ℝ (uncurry Y) (t, phi t) with hLdef
  have h1 : HasDerivAt (fun r => Y r (phi t)) (L (1, 0)) t := by
    have hc : HasDerivAt (fun r : ℝ => (r, phi t)) ((1 : ℝ), (0 : ℝ)) t :=
      HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t (phi t))
    exact hL.comp_hasDerivAt t hc
  have h2 : HasDerivAt (Y t) (L (0, 1)) (phi t) := by
    have hc : HasDerivAt (fun x : ℝ => (t, x)) ((0 : ℝ), (1 : ℝ)) (phi t) :=
      HasDerivAt.prodMk (hasDerivAt_const _ t) (hasDerivAt_id _)
    exact hL.comp_hasDerivAt _ hc
  have e1 : L (1, 0) = Yt t (phi t) := h1.unique (hYt t (phi t))
  have e2 : L (0, 1) = tauY t (phi t) := h2.unique (hYx t (phi t))
  have hc : HasDerivAt (fun r : ℝ => (r, phi r)) ((1 : ℝ), phi') t :=
    HasDerivAt.prodMk (hasDerivAt_id t) hphi
  have h := hL.comp_hasDerivAt t hc
  have hsplit : L ((1 : ℝ), phi') = L (1, 0) + phi' • L (0, 1) := by
    rw [← L.map_smul, ← L.map_add]
    norm_num
  rw [hsplit, e1, e2] at h
  exact h

/-- The space derivative of a `C¹` family is jointly continuous. -/
theorem continuous_partial_space {Y tauY : ℝ → ℝ → ℂ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x) : Continuous (uncurry tauY) := by
  have hfd : Continuous fun z : ℝ × ℝ => fderiv ℝ (uncurry Y) z := by
    simpa using hY.continuous_fderiv (by norm_num)
  have heq : uncurry tauY = fun z : ℝ × ℝ => (fderiv ℝ (uncurry Y) z) (0, 1) := by
    funext z
    obtain ⟨t, x⟩ := z
    have hL := ((hY.differentiable (by norm_num)) (t, x)).hasFDerivAt
    have h2 : HasDerivAt (Y t) ((fderiv ℝ (uncurry Y) (t, x)) (0, 1)) x := by
      have hc : HasDerivAt (fun y : ℝ => (t, y)) ((0 : ℝ), (1 : ℝ)) x :=
        HasDerivAt.prodMk (hasDerivAt_const _ t) (hasDerivAt_id _)
      exact hL.comp_hasDerivAt _ hc
    exact (hYx t x).unique h2
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), (1 : ℝ))).continuous.comp hfd

/-- The time derivative of a `C¹` family is jointly continuous. -/
theorem continuous_partial_time {Y Yt : ℝ → ℝ → ℂ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x) (Yt t x) t) : Continuous (uncurry Yt) := by
  have hfd : Continuous fun z : ℝ × ℝ => fderiv ℝ (uncurry Y) z := by
    simpa using hY.continuous_fderiv (by norm_num)
  have heq : uncurry Yt = fun z : ℝ × ℝ => (fderiv ℝ (uncurry Y) z) (1, 0) := by
    funext z
    obtain ⟨t, x⟩ := z
    have hL := ((hY.differentiable (by norm_num)) (t, x)).hasFDerivAt
    have h1 : HasDerivAt (fun r => Y r x) ((fderiv ℝ (uncurry Y) (t, x)) (1, 0)) t := by
      have hc : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ)) t :=
        HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t x)
      exact hL.comp_hasDerivAt t hc
    exact (hYt t x).unique h1
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ))).continuous.comp hfd

/-- **The normal component of the motion of a `C¹` family is jointly
continuous.** -/
theorem continuous_normal_component {Y tauY : ℝ → ℝ → ℂ} {xi eta : ℝ → ℝ → ℝ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((xi t x : ℂ) * tauY t x + (eta t x : ℂ) * (Complex.I * tauY t x)) t)
    (htau0 : ∀ t x, tauY t x ≠ 0) : Continuous (uncurry eta) := by
  set Yt : ℝ → ℝ → ℂ := fun t x =>
    (xi t x : ℂ) * tauY t x + (eta t x : ℂ) * (Complex.I * tauY t x) with hYtdef
  have hYtc : Continuous (uncurry Yt) := continuous_partial_time hY hYt
  have htauc : Continuous (uncurry tauY) := continuous_partial_space hY hYx
  have heq : uncurry eta = fun z : ℝ × ℝ => (uncurry Yt z / uncurry tauY z).im := by
    funext z
    obtain ⟨t, x⟩ := z
    have h : Yt t x / tauY t x = (xi t x : ℂ) + (eta t x : ℂ) * Complex.I := by
      rw [hYtdef, div_eq_iff (htau0 t x)]
      ring
    simp [uncurry, h]
  rw [heq]
  exact Complex.continuous_im.comp (hYtc.div htauc (fun z => htau0 z.1 z.2))

/-! ### The gauge flow of a bundle of frame data -/

/-- **The gauge flow of a bundle of frame data**, started from the parameter
rescaled by `ℓ`. -/
theorem exists_gaugeFlow_of_frameData (D : GaugeFrameData) {ell : ℝ} (hell : 0 < ell) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = ell * u) ∧
      ∀ u t, HasDerivAt (fun r => Phi r u) (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t := by
  obtain ⟨Phi, h0, hd, -⟩ := GaugeFlowSmooth.exists_gaugeFlow_smooth_of_bounds
    D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
    D.hv2c D.hrate1 D.hrate2 hell
  exact ⟨Phi, h0, hd⟩

/-! ### The path-metric bound from the family of rear tracks -/

/-- **The path pseudodistance of the selected rears, read off the family of
rear tracks.**

The family `Y` of rear tracks is written in its own arclength, closes up with
period `Q t`, and moves with tangential component `ξ` (the one of the frame
bundle `D`) and normal component `η_R`, the periodic solution of the inverse
Jacobi ODE of the front.  Then there is a gauge parameter `Φ` — equal to the
rescaled arclength at time `0` — in which the family is a normal path, and the
marked curve it reaches at time `T` is within
`gaugeJacobiConst · cost Γ` of the one it starts from. -/
theorem pathDist_le_of_rear_family {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {Y tauY : ℝ → ℝ → ℂ}
    (D : GaugeFrameData) {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the steering equation on the selected strip
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    -- the front normal velocity
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the change of variable and the inverse Jacobi ODE
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, etaR t = fun _ => 0)
    -- the rear period
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    -- the family of rear tracks, in its own arclength
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hstart : ∀ u, p'.1 u = Y 0 (Qf 0 * u)) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Qf 0 * u) ∧
      ((∀ t, D.xi t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = Y Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T (Qf 0) * cost Γ := by
  -- the tangent never vanishes
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t x h
    have hn := htaunorm t x
    rw [h] at hn
    simp at hn
  -- the tangent is periodic with the rear period, by differentiating the closing relation
  have htauper : ∀ t, Function.Periodic (tauY t) (Qf t) := by
    intro t x
    have hshift : HasDerivAt (fun y => Y t (y + Qf t)) (tauY t (x + Qf t)) x :=
      HasDerivAt.comp_add_const x (Qf t) (hYx t (x + Qf t))
    have hfun : (fun y => Y t (y + Qf t)) = Y t := funext fun y => hclose t y
    rw [hfun] at hshift
    exact hshift.unique (hYx t x)
  -- the normal velocity is periodic with the rear period, by the closing relations
  have hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t) := fun t x =>
    (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).2
  -- the rear period at time zero is positive
  have hQ0 : 0 < Qf 0 := by
    rw [hQdef 0]
    exact SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl 0)) hkh0 hkh1
      (SelectedPathData.continuous_of_steering (hsteer 0)) (hstrip0 0) (hstrip1 0)
  -- the gauge flow
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hQ0
  have hPhic : ∀ u, Continuous fun t => Phi t u := by
    intro u
    have hd : Differentiable ℝ fun t => Phi t u := fun t => (hPhid u t).differentiableAt
    exact hd.continuous
  -- the moving marked curve and its unit normal
  set XR : ℝ → ℝ → ℂ := fun t u => Y t (Phi t u) with hXRdef
  set nuR : ℝ → ℝ → ℂ := fun t u => Complex.I * tauY t (Phi t u) with hnuRdef
  have hnu : ∀ t u, ‖nuR t u‖ = 1 := by
    intro t u
    rw [hnuRdef]
    simp [htaunorm]
  -- the velocity of the moving marked curve is normal
  have hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t := by
    intro t u
    have h := hasDerivAt_along_curve (Y := Y) (tauY := tauY)
      (Yt := fun t x => (D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x))
      hY hYx hYt (hPhid u t)
    refine h.congr_deriv ?_
    rw [hnuRdef, GaugeRate.gaugeRate, hv1]
    simp only [div_one, Complex.real_smul, Complex.ofReal_neg]
    ring
  -- and it depends continuously on the time
  have hetaRc : Continuous (uncurry etaR) :=
    continuous_normal_component hY hYx hYt htau0
  have htauc : Continuous (uncurry tauY) := continuous_partial_space hY hYx
  have hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u := by
    intro u
    have h1 : Continuous fun t => etaR t (Phi t u) :=
      hetaRc.comp (continuous_id.prodMk (hPhic u))
    have h2 : Continuous fun t => tauY t (Phi t u) :=
      htauc.comp (continuous_id.prodMk (hPhic u))
    rw [hnuRdef]
    exact (Complex.continuous_ofReal.comp h1).mul (continuous_const.mul h2)
  refine ⟨Phi, fun u => hPhi0 u, ?_, ?_⟩
  · intro hxi0 t
    exact GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by simp [hPhi0 0]) hxi0 t
  intro q' hq'
  exact pathDist_le_of_gauge_geometry_front (etaY := etaR) (sf := sf) (etaFs := etaFs)
    (K := K) (XR := XR) (nuR := nuR) (Qf' := Qf') Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper hlink hv1
    hY hYx hYt htau0 htauper hclose hPhid hPhi0
    (fun u => by simp only [hXRdef]; rw [hPhi0 u, hstart u])
    (fun u => by simp only [hXRdef]; rw [hq' u]) hderiv hcont hnu hrest

/-- **The path pseudodistance of the selected rears, with the rear period
differentiated rather than assumed differentiable.**

Same as `pathDist_le_of_rear_family`, with the differentiability in the time of
the rear period `Q t = ∫₀^{P t} cos δ(t,·)` replaced by its ingredients: the
front period is differentiable, the cosine of the steering angle is Lipschitz in
the time uniformly in the arclength, and the fixed-endpoint integral may be
differentiated under the integral sign (`RearPeriodDeriv.lean`). -/
theorem pathDist_le_of_rear_family_periodDeriv {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh L : ℝ} {P P' : ℝ → ℝ} {delta K etaF etaFs etaR sf dtc : ℝ → ℝ → ℝ}
    {Y tauY : ℝ → ℝ → ℂ}
    (D : GaugeFrameData)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, etaR t = fun _ => 0)
    -- the rear period, differentiated
    (hPd : ∀ t, HasDerivAt P (P' t) t)
    (hlip : ∀ t r s, |Real.cos (delta r s) - Real.cos (delta t s)| ≤ L * |r - t|)
    (hparam : ∀ t, HasDerivAt (fun r => ∫ s in (0:ℝ)..(P t), Real.cos (delta r s))
      (∫ s in (0:ℝ)..(P t), dtc t s) t)
    -- the family of rear tracks, in its own arclength
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + rearArclength (delta t) (P t)) = Y t x)
    (hstart : ∀ u, p'.1 u = Y 0 (rearArclength (delta 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (delta 0) (P 0) * u) ∧
      ((∀ t, D.xi t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = Y Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T
            (rearArclength (delta 0) (P 0)) * cost Γ :=
  pathDist_le_of_rear_family Γ p' D (Qf := fun t => rearArclength (delta t) (P t))
    (Qf' := fun t => Real.cos (delta t (P t)) * P' t + ∫ s in (0:ℝ)..(P t), dtc t s)
    hP0 hkh0 hkh1 hPl hPu hsteer hstrip0 hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper
    hlink hsfinv hetaR hrest (fun _ => rfl)
    (fun t => RearPeriodDeriv.hasDerivAt_rearPeriod (t0 := t) (L := L)
      (fun r => SelectedPathData.continuous_of_steering (hsteer r)) (hlip t) (hPd t)
      (hparam t))
    hv1 hY hYx hYt htaunorm hclose hstart

/-- **The hypotheses are consistent.**  The constant path of fronts of curvature
`1/2` has steering angle `arcsin ½`, rear period `c = cos(arcsin ½)` and, as its
family of selected rears, the circle of circumference `c` at rest, written in
its own arclength.  All the hypotheses hold for that family, so the statement is
not vacuous. -/
example (p : Data) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = Real.sqrt (1 - (1/2 : ℝ) ^ 2) * u) ∧
      ((∀ t, trivialFrame.xi t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data,
        (∀ u, q'.1 u =
            ((Real.sqrt (1 - (1/2 : ℝ) ^ 2) / (2 * Real.pi) : ℝ) : ℂ) *
              Complex.exp (Complex.I *
                ((Phi (NormalPath.const p).T u
                  / (Real.sqrt (1 - (1/2 : ℝ) ^ 2) / (2 * Real.pi)) : ℝ) : ℂ))) →
        pathDist (circleData
              (Real.sqrt (1 - (1/2 : ℝ) ^ 2) / (2 * Real.pi))) q' ≤
          gaugeJacobiConst 1 1 (1/2) trivialFrame.rateLip trivialFrame.rateBound2
              (NormalPath.const p).T (Real.sqrt (1 - (1/2 : ℝ) ^ 2)) *
            cost (NormalPath.const p) := by
  set A : ℝ := Real.arcsin (1/2) with hA
  have hsinA : Real.sin A = 1/2 := Real.sin_arcsin (by norm_num) (by norm_num)
  set c : ℝ := Real.sqrt (1 - (1/2 : ℝ) ^ 2) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  have hcosA : Real.cos A = c := by rw [hA, Real.cos_arcsin]
  have hArc : rearArclength (fun _ : ℝ => A) = fun y => y * c := by
    funext y
    simp [rearArclength, hcosA]
  set R : ℝ := c / (2 * Real.pi) with hR
  have hRpos : 0 < R := by
    rw [hR]
    have := Real.pi_pos
    positivity
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hcR : c / R = 2 * Real.pi := by
    rw [hR]
    have := Real.pi_pos
    field_simp
  set Y : ℝ → ℝ → ℂ := fun _ x => (R : ℂ) * Complex.exp (Complex.I * ((x / R : ℝ) : ℂ))
    with hYdef
  set tauY : ℝ → ℝ → ℂ := fun _ x => Complex.I * Complex.exp (Complex.I * ((x / R : ℝ) : ℂ))
    with htauYdef
  have hshift : ∀ x : ℝ, Complex.exp (Complex.I * (((x + c) / R : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((x / R : ℝ) : ℂ)) := by
    intro x
    have h1 : (((x + c) / R : ℝ) : ℂ) = ((x / R : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) := by
      have h2 : (x + c) / R = x / R + 2 * Real.pi := by rw [add_div, hcR]
      rw [h2]
      push_cast
      ring
    rw [h1, mul_add, Complex.exp_add,
      show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one]
  refine pathDist_le_of_rear_family (NormalPath.const p) _ (P0 := 1) (P1 := 1) (kh := 1/2)
    (P := fun _ => 1) (delta := fun _ _ => A) (K := fun _ _ => 1/2)
    (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0) (etaR := fun _ _ => 0)
    (sf := fun _ x => x / c) (Y := Y) (tauY := tauY)
    trivialFrame (Qf := fun _ => c) (Qf' := fun _ => 0)
    one_pos (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ s => (hasDerivAt_const s A).congr_deriv (by rw [hsinA]; ring))
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num) (fun _ => continuous_const)
    (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ => continuous_const) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ x => by rw [hArc]; field_simp)
    (fun _ x => (hasDerivAt_const x (0:ℝ)).congr_deriv (by simp))
    (fun _ _ => rfl)
    (fun t => by rw [hArc]; ring)
    (fun t => hasDerivAt_const t c) (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · -- the family is `C¹`
    have h : Function.uncurry Y
        = fun z : ℝ × ℝ => (R : ℂ) * Complex.exp (Complex.I * ((z.2 / R : ℝ) : ℂ)) := rfl
    rw [h]
    have h1 : ContDiff ℝ (1:ℕ) (fun z : ℝ × ℝ => (z.2 / R : ℝ)) :=
      contDiff_snd.div_const R
    have h2 : ContDiff ℝ (1:ℕ) (fun z : ℝ × ℝ => ((z.2 / R : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    exact contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul h2))
  · -- its space derivative is the tangent
    intro t x
    have h1 : HasDerivAt (fun y : ℝ => ((y / R : ℝ) : ℂ)) (((1 / R : ℝ) : ℂ)) x := by
      simpa using (((hasDerivAt_id x).div_const R)).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => Complex.I * ((y / R : ℝ) : ℂ))
        (Complex.I * ((1 / R : ℝ) : ℂ)) x := h1.const_mul Complex.I
    have h3 := (h2.cexp).const_mul (R : ℂ)
    refine h3.congr_deriv ?_
    rw [htauYdef]
    simp only
    push_cast
    field_simp
  · -- the family is at rest
    intro t x
    refine (hasDerivAt_const t (Y t x)).congr_deriv ?_
    simp [trivialFrame]
  · -- the parameter is the arclength of the slices
    intro t x
    rw [htauYdef]
    simp [Complex.norm_exp]
  · -- the slices close up
    intro t x
    rw [hYdef]
    simp only
    rw [hshift x]
  · -- the initial slice is the circle in the rescaled arclength
    intro u
    rw [hYdef]
    simp only [circleData_fst, normExp]
    congr 2
    rw [show c * u / R = 2 * Real.pi * u by rw [mul_comm c u, mul_div_assoc, hcR]; ring]
    push_cast
    ring

end GaugePathRearFamily
