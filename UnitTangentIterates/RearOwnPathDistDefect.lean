import Mathlib
import UnitTangentIterates.RearOwnPathDist
import UnitTangentIterates.GaugePathRearFamilyDefect

/-!
# The path pseudodistance of the selected rears from the front data, with the
defect of its gauge marking

`RearOwnPathDist.pathDist_le_of_front_family` removes the family of rear tracks
from the hypotheses of `GaugePathRearFamily.pathDist_le_of_rear_family`: the
family is constructed from the front as `R(t, sf(t,x))`.  Its conclusion
exposes the gauge marking `Φ` but says nothing about `Φ` as a
parametrization.

This file is the same step applied to
`GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family`: for the same
`Φ`, and under the same extra hypotheses (the gauge normalization
`ξ(t,0) = 0`, a bound `C t ≤ κ·m t` for the arclength derivative of the
tangential component, and an upper bound `L_max` for the rear period), the
marking fixes the base point, reads exactly one period, and deviates from the
affine marking of the terminal period by at most `2 L_max κ · cost Γ`.

Main result: `pathDist_and_defect_le_of_front_family`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistDefect

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugePathRearFamily GaugePathDistVariable GaugeGeometryPathVariable

/-- **The path pseudodistance of the selected rears of a path of fronts,
together with the defect of the gauge marking in which it is read.**
Everything asked of the rears is a property of the *front* data, as in
`RearOwnPathDist.pathDist_le_of_front_family`; on top of that conclusion the
gauge marking is now known to fix the base point, to read exactly one rear
period, and to deviate from the affine marking of the terminal period by at
most `2 L_max κ · cost Γ`. -/
theorem pathDist_and_defect_le_of_front_family {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Gdot Ydot : ℝ → ℝ → ℂ} {Θ δ K etaF etaFs sf sft dt : ℝ → ℝ → ℝ}
    {vdot psidot xix etax : ℝ → ℝ → ℝ}
    (D : GaugeFrameData)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the front, its tangent angle and its selected steering angle
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    -- the regularity of the front data
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ))
    (hδt : ∀ t s, HasDerivAt (fun r => δ r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    -- the normal velocity of the front
    (hetaFdef : ∀ t s, etaF t s = frontNormalVelocityAt Fdot Θ δ t s)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the change of variable
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    -- the motion of the family of rear tracks
    (hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s) (Gdot t s) t)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hYdot : ∀ t x, Ydot t x = Gdot t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    -- the regularity of the frozen families
    (hR2 : ∀ t, ContDiff ℝ 2 (uncurry (rearFamily F Θ δ (sf t))))
    (hv : ∀ t x, HasDerivAt (fun a' => frameSpeed δ (sf t) t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => frameAngle Θ δ (sf t) a' x) (psidot t x) t)
    (hxi : ∀ t x, HasDerivAt
      (fun x' => frameTangential (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (xix t x) x)
    (heta : ∀ t x, HasDerivAt
      (fun x' => frameNormal (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (etax t x) x)
    -- the frame data of the family
    (hv1 : ∀ t x, D.v t x = 1)
    (hxiD : ∀ t x, D.xi t x = frameTangential Ydot (rearOwnAngle Θ δ sf) t x)
    -- the path is at rest outside its interval of definition
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    -- the rear period
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    -- the gauge normalization and the growth of the tangential component
    (hxi0 : ∀ t, D.xi t 0 = 0) {C : ℝ → ℝ} {Lmax kappa : ℝ}
    (hxi1bd : ∀ t x, |D.xi1 t x| ≤ C t) (hCcont : Continuous C)
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Lmax)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  -- the rear speed is positive on the selected strip
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  -- the change of variable, and its regularity
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hsfC : ContDiff ℝ 1 (uncurry sf) :=
    SelectedChangeOfVariable.contDiff_one_sf hkh0 hkh1 hδcont hδt hdtc hstrip0 hstrip1 hsfinv
  -- the family of rear tracks, in its own arclength
  have hYC : ContDiff ℝ 1 (uncurry (rearOwn F Θ δ sf)) :=
    contDiff_one_rearOwn hFC hΘC hδC hsfC
  have hYx : ∀ t x, HasDerivAt (rearOwn F Θ δ sf t) (rearOwnTangent Θ δ sf t x) x :=
    fun t x => hasDerivAt_rearOwn_space hF hΘ hsteer hsfspace hcos t x
  have hGC : ContDiff ℝ (1 : ℕ) (uncurry (frontParamTrack F Θ δ)) := by
    simpa [frontParamTrack] using contDiff_one_rearTrackFamily hFC hΘC hδC
  have hGx : ∀ t s, HasDerivAt (frontParamTrack F Θ δ t)
      ((Real.cos (δ t s) : ℂ) * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))) s :=
    fun t s => hasDerivAt_rearTrack (F := F t) (Θ := Θ t) (δ := δ t) (K := K t)
      (hF t s) (hΘ t s) (hsteer t s)
  have hYd : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t := by
    intro t x
    have h := hasDerivAt_rearOwn_time (Gdot := Gdot) (sft := sft) hGC hGx hGt hsft t x
    rw [hYdot t x]
    exact h
  -- the motion in the moving frame
  have hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((D.xi t x : ℂ) * rearOwnTangent Θ δ sf t x
        + ((frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℝ) : ℂ)
          * (Complex.I * rearOwnTangent Θ δ sf t x)) t := by
    intro t x
    rw [hxiD t x]
    exact hasDerivAt_rearOwn_time_frame (hYd t x)
  -- the inverse Jacobi ODE for the normal velocity
  have hetaR : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x := by
    intro t x
    have h := hasDerivAt_rearOwn_normal_jacobi (F := F) (Θ := Θ) (δ := δ) (K := K)
      (sf := sf) (sft := sft) (Gdot := Gdot) (Fdot := Fdot)
      (vdot := vdot) (psidot := psidot) (xix := xix) (etax := etax)
      Ydot hF hΘ hsteer hsfspace hcos hGt hFa hR2 hv hpsia hxi heta hYdot t x
    rwa [hetaFdef t (sf t x)]
  -- the closing relation
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwn F Θ δ sf t x :=
    fun t x => rearOwn_closing hkh0 hkh1 hδslice hstrip0 hstrip1 hdper hsfinv hFper hΘper t x
  exact GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family Γ p' D
    (Qf := fun t => rearArclength (δ t) (P t))
    (Qf' := Qf') (delta := δ) (K := K) (etaF := etaF) (etaFs := etaFs)
    (etaR := fun t x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) (sf := sf)
    (Y := rearOwn F Θ δ sf) (tauY := rearOwnTangent Θ δ sf)
    hP0 hkh0 hkh1 hPl hPu hsteer hstrip0 hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper
    hlink hsfinv hetaR hrest (fun _ => rfl) hQd hv1 hYC hYx hYt
    (fun t x => norm_rearOwn_tangent t x) hclose hstart hxi0 hxi1bd hCcont hQmax hcost

/-- **The path pseudodistance of the selected rears from smooth dependence of the
front data, together with the defect of the gauge marking.**  Same as
`RearOwnPathDist.pathDist_le_of_front_smoothDependence`, with the marking now
known to fix the base point (the base drift of the front vanishing), to read
exactly one rear period, and to deviate from the affine marking of the terminal
period by at most `2 L_max κ · cost Γ`. -/
theorem pathDist_and_defect_le_of_front_smoothDependence {p q : Data} (Γ : NormalPath p q)
    (p' : Data) {P0 P1 kh : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Fdots Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF etaFs sf sft dt Θdot w Θdots ws : ℝ → ℝ → ℝ}
    (D : GaugeFrameData)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ))
    (hδt : ∀ t s, HasDerivAt (fun r => δ r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    (hetaFdef : ∀ t s, etaF t s = frontNormalVelocityAt Fdot Θ δ t s)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    -- the smooth dependence of the front data on the path parameter
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hΘa : ∀ t s, HasDerivAt (fun r => Θ r s) (Θdot t s) t)
    (hδa : ∀ t s, HasDerivAt (fun r => δ r s) (w t s) t)
    (hFdots : ∀ t s, HasDerivAt (Fdot t) (Fdots t s) s)
    (hΘdots : ∀ t s, HasDerivAt (Θdot t) (Θdots t s) s)
    (hws : ∀ t s, HasDerivAt (w t) (ws t s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F)) (hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ))
    (hδc2 : ContDiff ℝ (2 : ℕ) (uncurry δ))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hv1 : ∀ t x, D.v t x = 1)
    (hxiD : ∀ t x, D.xi t x = frameTangential Ydot (rearOwnAngle Θ δ sf) t x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    -- the gauge normalization and the growth of the tangential component
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0)
    {C : ℝ → ℝ} {Lmax kappa : ℝ}
    (hxi1bd : ∀ t x, |D.xi1 t x| ≤ C t) (hCcont : Continuous C)
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Lmax)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  -- the base drift of the front is the tangential component at the base point
  have hxi0 : ∀ t, D.xi t 0 = 0 := fun t =>
    (hxiD t 0).trans ((RearBaseDrift.frameTangential_rearOwn_base (kh := kh) hkh0 hkh1
      (fun _ => hδcont.comp (continuous_const.prodMk continuous_id)) hstrip0 hstrip1 hsfinv
      hsft hYdot t).trans (hdrift t))
  exact pathDist_and_defect_le_of_front_family Γ p'
    (Gdot := trackVelocity Fdot Θdot w Θ δ)
    (Fdot := Fdot) (Ydot := Ydot) (sft := sft) (dt := dt)
    (vdot := fun t x => -(Real.sin (δ t (sf t x)) * w t (sf t x)) / Real.cos (δ t (sf t x)))
    (psidot := fun t x => Θdot t (sf t x) - w t (sf t x))
    (xix := fun t x =>
      ((((1 / Real.cos (δ t (sf t x)) : ℝ) : ℂ) * Fdots t (sf t x))
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ (sf t) t x : ℂ)))).re
        + Real.tan (δ t (sf t x))
          * (Fdot t (sf t x)
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ (sf t) t x : ℂ)))).im)
    (etax := fun t x =>
      ((((1 / Real.cos (δ t (sf t x)) : ℝ) : ℂ) * Fdots t (sf t x))
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ (sf t) t x : ℂ)))).im
        - Real.tan (δ t (sf t x))
          * (Fdot t (sf t x)
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ (sf t) t x : ℂ)))).re
        - (Θdots t (sf t x) - ws t (sf t x)) * (1 / Real.cos (δ t (sf t x))))
      D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
      hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
      (fun t s => hasDerivAt_frontParamTrack_time hFa hΘa hδa t s) hFa hYdot
      (fun t => RearFrameRegularity.contDiff_two_rearFamily (a0 := t) hFc2 hΘc2 hδc2
      (fun y => hcos t y) (hsfspace t))
    (fun t x => RearFrameRegularity.hasDerivAt_frameSpeed_param (σ := sf t) (a0 := t)
      (w := w) hδa x)
    (fun t x => RearFrameRegularity.hasDerivAt_frameAngle_param (σ := sf t) (a0 := t)
      (Θdot := Θdot) (w := w) hΘa hδa x)
    (fun t x => RearFrameRegularity.hasDerivAt_frameTangential_rear (K := K) (σ := sf t)
      (a0 := t) (Fdot := Fdot) (Fdots := Fdots t) (Θdot := Θdot) (w := w)
      hΘ hsteer (hsfspace t) (hFdots t) x)
    (fun t x => RearFrameRegularity.hasDerivAt_frameNormal_rear (K := K) (σ := sf t)
      (a0 := t) (Fdot := Fdot) (Fdots := Fdots t) (Θdot := Θdot) (Θdots := Θdots t)
      (w := w) (ws := ws t) hΘ hsteer (hsfspace t) (hFdots t) (hΘdots t) (hws t) x)
    hv1 hxiD hrest hQd hstart hxi0 hxi1bd hCcont hQmax hcost

end RearOwnPathDistDefect
