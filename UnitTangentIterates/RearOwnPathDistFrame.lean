import Mathlib
import UnitTangentIterates.RearOwnPathDist
import UnitTangentIterates.RearOwnFrameData

/-!
# The path pseudodistance of the selected rears, with the frame bundle produced

`RearOwnPathDist.pathDist_le_of_front_smoothDependence` reduces every hypothesis
on the family of rear tracks to smooth dependence of the front data, but still
takes a bundle `UniformFrameBounds.GaugeFrameData` of frame data and constants,
asked to have unit speed and to carry the tangential component of the family.

Here that bundle is produced as well.  By
`GaugePeriodRigidity.rearFamily_period_constant` such a bundle can only exist
when the rear arclength period is the same at every time, so that period is
taken as a hypothesis; the tangential component of the family is then periodic
in the rear arclength — the velocity is periodic because the closing relation no
longer moves, and the rear tangent angle turns by `2π` over one period — and
`RearOwnFrameData.exists_gaugeFrameData_frameTangential` builds the bundle.

Main result: `pathDist_le_of_front_frame`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrame

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameData

variable {F Fdot Ydot : ℝ → ℝ → ℂ} {Θ δ sf : ℝ → ℝ → ℝ}

/-! ### The rear tangent angle over one rear period -/

/-- **The rear tangent angle turns by `2π` over one rear period.** -/
theorem rearOwnAngle_shift {kh : ℝ} {P : ℝ → ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδslice : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi) (t x : ℝ) :
    rearOwnAngle Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwnAngle Θ δ sf t x + 2 * Real.pi := by
  have hshift : sf t (x + rearArclength (δ t) (P t)) = sf t x + P t :=
    SelectedPathData.sf_add_rearPeriod hkh0 hkh1 (hδslice t) (hstrip0 t) (hstrip1 t)
      (hdper t) (hsfinv t) x
  simp only [rearOwnAngle, rearAngle, hshift, hΘper t (sf t x), hdper t (sf t x)]
  ring

/-! ### The path pseudodistance with the frame bundle produced -/

/-- **The path pseudodistance of the selected rears of a path of fronts, with
the gauge frame bundle constructed rather than assumed.**

Every hypothesis is now on the front data — its geometry, its regularity and its
smooth dependence on the path parameter — together with the two structural
requirements that make the bundle exist at all: the rear arclength period is the
same at every time (which `GaugePeriodRigidity.rearFamily_period_constant` shows
is forced), and the family is at rest outside the time window of the path. -/
theorem pathDist_le_of_front_frame {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh Q : ℝ} {P : ℝ → ℝ}
    {Fdots : ℝ → ℝ → ℂ}
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
    -- the rear period is the same at every time
    (hQpos : 0 < Q) (hQconst : ∀ t, rearArclength (δ t) (P t) = Q)
    -- the regularity of the velocity and of the rear tangent angle
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    -- the family is at rest outside the time window of the path
    (hfrozenY : ∀ a x, Ydot a x = Ydot (clampT 0 Γ.T a) x)
    (hfrozenA : ∀ a x, rearOwnAngle Θ δ sf a x = rearOwnAngle Θ δ sf (clampT 0 Γ.T a) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (Q * u)) :
    ∃ (rL rB : ℝ) (Phi : ℝ → ℝ → ℝ), (∀ u, Phi 0 u = Q * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh rL rB Γ.T Q * cost Γ := by
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  -- the closing relation of the family, with the constant period
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + Q) = rearOwn F Θ δ sf t x := by
    intro t x
    have := rearOwn_closing (kap := kh) (P := P) hkh0 hkh1 hδslice hstrip0 hstrip1 hdper
      hsfinv hFper hΘper t x
    rwa [hQconst t] at this
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
  -- the velocity is periodic, because the closing relation does not move
  have hYper : ∀ t, Function.Periodic (Ydot t) Q := by
    intro t x
    have h1 : HasDerivAt (fun r => rearOwn F Θ δ sf r (x + Q)) (Ydot t (x + Q)) t :=
      hYd t (x + Q)
    have hfun : (fun r => rearOwn F Θ δ sf r (x + Q)) = fun r => rearOwn F Θ δ sf r x :=
      funext fun r => hclose r x
    rw [hfun] at h1
    exact h1.unique (hYd t x)
  -- the rear tangent angle turns by `2π` over one rear period
  have hangper : ∀ t x, rearOwnAngle Θ δ sf t (x + Q)
      = rearOwnAngle Θ δ sf t x + 2 * Real.pi := by
    intro t x
    have := rearOwnAngle_shift (kh := kh) (P := P) hkh0 hkh1 hδslice hstrip0 hstrip1
      hdper hsfinv hΘper t x
    rwa [hQconst t] at this
  -- the gauge frame bundle
  obtain ⟨D, hv1, hxiD⟩ := exists_gaugeFrameData_frameTangential (t0 := 0) (t1 := Γ.T)
    hQpos Γ.T_pos.le hYdotC hangC hYper hangper hfrozenY hfrozenA
  refine ⟨D.rateLip, D.rateBound2, ?_⟩
  have hQ0 : rearArclength (δ 0) (P 0) = Q := hQconst 0
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ := pathDist_le_of_front_smoothDependence Γ p'
    (Fdot := Fdot) (Fdots := Fdots) (Ydot := Ydot) (Qf' := fun _ => 0)
    (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt) (sft := sft)
    (K := K) (etaF := etaF) (etaFs := etaFs)
    D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hv1 hxiD hrest
    (fun t => by
      have hcst : (fun r => rearArclength (δ r) (P r)) = fun _ : ℝ => Q := funext hQconst
      rw [hcst]
      exact hasDerivAt_const t Q)
    (fun u => by rw [hstart u, ← hQ0])
  refine ⟨Phi, fun u => by rw [hPhi0 u, hQ0], hbase, fun q' hq' => ?_⟩
  have := hPhi q' hq'
  rwa [hQ0] at this

/-- **The structural hypotheses of `pathDist_le_of_front_frame` are
consistent.**  The circle of curvature `1/2`, at rest, has constant rear
arclength period `4π cos(arcsin ½)`, velocity zero — hence smooth, periodic and
frozen — and a rear tangent angle which is smooth and independent of the time,
so the hypotheses that the frame bundle is built from are not contradictory.
(The remaining, front-side hypotheses are checked for the same curve in
`RearOwnPathDist.front_hypotheses_consistent`.) -/
theorem frame_hypotheses_consistent :
    ∃ (Θ δ sf : ℝ → ℝ → ℝ) (P : ℝ → ℝ) (Ydot : ℝ → ℝ → ℂ) (Q T : ℝ),
      0 < T ∧ 0 < Q ∧ (∀ t, rearArclength (δ t) (P t) = Q) ∧
      ContDiff ℝ (3 : ℕ) (uncurry Ydot) ∧
      ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) ∧
      (∀ a x, Ydot a x = Ydot (clampT 0 T a) x) ∧
      (∀ a x, rearOwnAngle Θ δ sf a x = rearOwnAngle Θ δ sf (clampT 0 T a) x) ∧
      (∀ t x, frameNormal Ydot (rearOwnAngle Θ δ sf) t x = 0) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      (∀ t, Function.Periodic (δ t) (P t)) := by
  set A : ℝ := Real.arcsin (1 / 2) with hA
  set c : ℝ := Real.cos A with hc
  have hcval : c = Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := by rw [hc, hA, Real.cos_arcsin]
  have hcpos : 0 < c := by rw [hcval]; positivity
  refine ⟨fun _ s => s / 2, fun _ _ => A, fun _ x => x / c, fun _ => 4 * Real.pi,
    fun _ _ => 0, 4 * Real.pi * c, 1, one_pos, by positivity, ?_, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, fun _ _ => rfl⟩
  · intro t
    show rearArclength (fun _ => A) (4 * Real.pi) = 4 * Real.pi * c
    simp only [rearArclength]
    rw [intervalIntegral.integral_const]
    simp [← hc]
  · exact contDiff_const
  · have : uncurry (rearOwnAngle (fun _ s => s / 2) (fun _ _ => A) (fun _ x => x / c))
        = fun p : ℝ × ℝ => p.2 / c / 2 - A := rfl
    rw [this]
    exact ((contDiff_snd.div_const c).div_const 2).sub contDiff_const
  · intro t x
    simp [frameNormal]
  · intro t x
    show rearArclength (fun _ => A) (x / c) = x
    simp only [rearArclength]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, ← hc]
    field_simp

end RearOwnPathDistFrame
