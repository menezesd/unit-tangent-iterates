import Mathlib
import UnitTangentIterates.RearOwnPathDistFrame
import UnitTangentIterates.RearOwnFrameDrift

/-!
# The path pseudodistance of the selected rears, with the length of the rear
free to move

`RearOwnPathDistFrame.pathDist_le_of_front_frame` states the path-metric bound
for the selected rears with the gauge frame bundle constructed rather than
assumed, but under one structural restriction: the arclength period of the rear
is the same at every time of the path.  That restriction came from the bundle,
which used to require a global bound on the tangential component of the motion,
and a family of closed curves written in its own arclength has such a bound only
when its length does not move (`GaugePeriodRigidity.lean`).

The bundle now asks only for bounds on the arclength derivatives of the
tangential *rate*, which for a unit-speed family are the arclength derivatives
of the tangential component, and those stay periodic however the length moves
(`RearOwnFrameDrift.lean`).  So the restriction disappears here: the rear period
`Q t = ∫₀^{P t} cos δ(t, ·)` is only asked to be differentiable in the time, and
the drift of the tangential component over one period — which is exactly `Q'(t)`,
by the closing relation of the family — is what the variable-period chain
(`GaugeFlowVariablePeriod.lean` and the files built on it) consumes.

Main result: `pathDist_le_of_front_frame_variable`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrameDrift

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  RearOwnPathDistFrame

/-- **The path pseudodistance of the selected rears of a path of fronts, with
the gauge frame bundle constructed and the length of the rear free to move.**

Every hypothesis is on the front data — its geometry, its regularity and its
smooth dependence on the path parameter — together with the requirement that the
family be at rest outside the time window of the path.  The rear arclength
period `Q t` is only asked to be differentiable in the time; nothing forces it
to be constant. -/
theorem pathDist_le_of_front_frame_variable {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Fdots Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF etaFs sf sft dt Θdot w Θdots ws : ℝ → ℝ → ℝ}
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
    -- the rear period moves differentiably
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    -- the regularity of the velocity and of the rear tangent angle
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    -- the family is at rest outside the time window of the path
    (hfrozenY : ∀ a x, Ydot a x = Ydot (clampT 0 Γ.T a) x)
    (hfrozenA : ∀ a x, rearOwnAngle Θ δ sf a x = rearOwnAngle Θ δ sf (clampT 0 Γ.T a) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ (rL rB : ℝ) (Phi : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh rL rB Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  set Qf : ℝ → ℝ := fun t => rearArclength (δ t) (P t) with hQfdef
  -- the rear period is positive and moves continuously
  have hQpos : ∀ t, 0 < Qf t := fun t =>
    SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl t)) hkh0 hkh1 (hδslice t)
      (hstrip0 t) (hstrip1 t)
  have hQc : Continuous Qf := by
    have : Differentiable ℝ Qf := fun t => (hQd t).differentiableAt
    exact this.continuous
  -- the family, its unit tangent and its closing relation
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hYx : ∀ t x, HasDerivAt (rearOwn F Θ δ sf t) (rearOwnTangent Θ δ sf t x) x :=
    hasDerivAt_rearOwn_space hF hΘ hsteer hsfspace hcos
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + Qf t) = rearOwn F Θ δ sf t x :=
    rearOwn_closing (kap := kh) (P := P) hkh0 hkh1 hδslice hstrip0 hstrip1 hdper hsfinv
      hFper hΘper
  have hsfC : ContDiff ℝ 1 (uncurry sf) :=
    SelectedChangeOfVariable.contDiff_one_sf hkh0 hkh1 hδcont hδt hdtc hstrip0 hstrip1 hsfinv
  have hYC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwn F Θ δ sf)) :=
    contDiff_one_rearOwn hFC hΘC hδC hsfC
  -- the velocity of the family
  have hGC : ContDiff ℝ (1 : ℕ) (uncurry (frontParamTrack F Θ δ)) := by
    simpa [frontParamTrack] using contDiff_one_rearTrackFamily hFC hΘC hδC
  have hGx : ∀ t s, HasDerivAt (frontParamTrack F Θ δ t)
      ((Real.cos (δ t s) : ℂ) * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))) s :=
    fun t s => hasDerivAt_rearTrack (F := F t) (Θ := Θ t) (δ := δ t) (K := K t)
      (hF t s) (hΘ t s) (hsteer t s)
  have hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s)
      (trackVelocity Fdot Θdot w Θ δ t s) t :=
    fun t s => hasDerivAt_frontParamTrack_time hFa hΘa hδa t s
  have hYd : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t := by
    intro t x
    have h := hasDerivAt_rearOwn_time (Gdot := trackVelocity Fdot Θdot w Θ δ) (sft := sft)
      hGC hGx hGt hsft t x
    rw [hYdot t x]
    exact h
  -- the frame decomposition of the velocity
  set psi : ℝ → ℝ → ℝ := rearOwnAngle Θ δ sf with hpsidef
  set xiF : ℝ → ℝ → ℝ := frameTangential Ydot psi with hxiFdef
  set etaF' : ℝ → ℝ → ℝ := frameNormal Ydot psi with hetaFdef'
  have hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((xiF t x : ℂ) * rearOwnTangent Θ δ sf t x
        + (etaF' t x : ℂ) * (Complex.I * rearOwnTangent Θ δ sf t x)) t := by
    intro t x
    have hrec : ((xiF t x : ℂ) + Complex.I * (etaF' t x : ℂ))
        * Complex.exp (Complex.I * (psi t x : ℂ)) = Ydot t x :=
      frame_reconstruct (Ydot t x) (psi t x)
    have heq : (xiF t x : ℂ) * rearOwnTangent Θ δ sf t x
        + (etaF' t x : ℂ) * (Complex.I * rearOwnTangent Θ δ sf t x) = Ydot t x := by
      rw [← hrec]
      simp only [rearOwnTangent, hpsidef]
      ring
    rw [heq]
    exact hYd t x
  have htau0 : ∀ t x, rearOwnTangent Θ δ sf t x ≠ 0 := by
    intro t x h
    have hn := norm_rearOwn_tangent (Θ := Θ) (δ := δ) (sf := sf) t x
    rw [h] at hn
    simp at hn
  -- the tangent is periodic, the tangent angle turning by `2π` over one period
  have hangshift : ∀ t x, psi t (x + Qf t) = psi t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift (kh := kh) (P := P) hkh0 hkh1 hδslice hstrip0
      hstrip1 hdper hsfinv hΘper t x
  have htauper : ∀ t, Function.Periodic (rearOwnTangent Θ δ sf t) (Qf t) := by
    intro t x
    have h2pi : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    simp only [rearOwnTangent, ← hpsidef, hangshift t x]
    push_cast
    rw [show Complex.I * ((psi t x : ℂ) + 2 * (Real.pi : ℂ))
        = Complex.I * (psi t x : ℂ) + Complex.I * ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, h2pi, mul_one]
  -- the closing relation makes the tangential component drift by `Q'(t)`
  have hxiqp : ∀ t x, xiF t (x + Qf t) = xiF t x - Qf' t := by
    intro t x
    exact (GaugeClosingRelations.closing_relations hYC hYx hYt htau0 htauper hclose hQd t x).1
  -- the gauge frame bundle
  obtain ⟨D, hv1, hxiD⟩ := exists_gaugeFrameData_frameTangential_drift (t0 := 0) (t1 := Γ.T)
    (P := Qf) (c := Qf') Γ.T_pos.le hQpos hQc hYdotC hangC hxiqp hfrozenY hfrozenA
  refine ⟨D.rateLip, D.rateBound2, ?_⟩
  exact pathDist_le_of_front_smoothDependence Γ p'
    (Fdot := Fdot) (Fdots := Fdots) (Ydot := Ydot) (Qf' := Qf')
    (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt) (sft := sft)
    (K := K) (etaF := etaF) (etaFs := etaFs)
    D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hv1 hxiD hrest hQd hstart

end RearOwnPathDistFrameDrift
