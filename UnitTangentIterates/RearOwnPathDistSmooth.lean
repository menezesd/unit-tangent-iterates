import Mathlib
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# The path pseudodistance of the selected rears, from the regularity of the
front alone

`RearOwnPathDistGeometric.pathDist_le_of_front_normalVelocity` produces every
*constant* of the path-metric bound from the front data, but it still asks two
regularity hypotheses about the rear side: the joint `C³` regularity of the
velocity `Ẏ` of the family of rear tracks written in its own arclength, and of
its tangent angle `Ψ`.

Here those two are discharged as well.  By `RearOwnHigherRegularity.lean` the
change of variable `sf` from the front to the rear arclength is as smooth as the
steering angle, the parameter derivatives `Ḟ`, `Θ̇`, `ẇ`, `∂_t sf` are one
derivative less smooth than the data they come from, and `Ẏ` and `Ψ` are built
from those by composition.  So joint `C⁴` regularity of the front `F`, of its
tangent angle `Θ` and of the selected steering angle `δ` suffices:
`pathDist_le_of_front_regularity` asks nothing at all about the rear family
beyond the equation `hYdot` that defines its velocity.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSmooth

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  RearOwnPathDistFrameBounds RearOwnTangential RearOwnPathDistGeometric
  RearOwnHigherRegularity

/-- **The path pseudodistance of the selected rears, with every constant and
every regularity hypothesis read off the front.**

The hypotheses of `RearOwnPathDistGeometric.pathDist_le_of_front_normalVelocity`
on the rear side — the joint `C³` regularity of the velocity of the family of
rear tracks written in its own arclength and of its tangent angle — are replaced
here by the joint `C⁴` regularity of the front `F`, of its tangent angle `Θ` and
of the selected steering angle `δ`.  The change of variable is as smooth as `δ`
(`RearOwnHigherRegularity.contDiff_sf`), the parameter derivatives lose one
derivative, and the rear data are assembled from them by composition. -/
theorem pathDist_le_of_front_regularity {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh EF : ℝ} {P Qf' : ℝ → ℝ}
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
    -- the regularity of the front data, in the pair
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hEF : ∀ t s, |etaF t s| ≤ EF)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  -- the front data, in the form the regularity lemmas expect
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hΘ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry Θ) := by norm_num; exact_mod_cast hΘc4
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hle31 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hle21 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (2 : ℕ) ≤ 4)
  have hle11 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 4)
  have hF3 : ContDiff ℝ (3 : ℕ) (uncurry F) := hFc4.of_le hle31
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle31
  have hδ3 : ContDiff ℝ (3 : ℕ) (uncurry δ) := hδc4.of_le hle31
  have hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F) := hFc4.of_le hle21
  have hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ) := hΘc4.of_le hle21
  have hδc2 : ContDiff ℝ (2 : ℕ) (uncurry δ) := hδc4.of_le hle21
  have hFC : ContDiff ℝ 1 (uncurry F) := by simpa using hFc4.of_le hle11
  have hΘC : ContDiff ℝ 1 (uncurry Θ) := by simpa using hΘc4.of_le hle11
  have hδC : ContDiff ℝ 1 (uncurry δ) := by simpa using hδc4.of_le hle11
  -- the change of variable and its parameter derivative
  have hsfC4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry sf) :=
    contDiff_sf hkh0 hkh1 hδ4 hstrip0 hstrip1 hsfinv
  have hsf3 : ContDiff ℝ (3 : ℕ) (uncurry sf) := by
    refine hsfC4.of_le ?_
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 3 + 1)
  have hsft3 : ContDiff ℝ (3 : ℕ) (uncurry sft) :=
    contDiff_partialTime_of_hasDerivAt hsfC4 hsft
  -- the parameter derivatives of the front data
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry Fdot) :=
    contDiff_partialTime_of_hasDerivAt hF4 hFa
  have hΘdot3 : ContDiff ℝ (3 : ℕ) (uncurry Θdot) :=
    contDiff_partialTime_of_hasDerivAt hΘ4 hΘa
  have hw3 : ContDiff ℝ (3 : ℕ) (uncurry w) :=
    contDiff_partialTime_of_hasDerivAt hδ4 hδa
  -- the rear data
  have hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    contDiff_rearOwnAngle hΘ3 hδ3 hsf3
  have hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot) :=
    contDiff_rearOwnVelocity hΘ3 hδ3 hsf3 hFdot3 hΘdot3 hw3 hsft3 hYdot
  exact pathDist_le_of_front_normalVelocity Γ p' (Qf' := Qf') (Fdots := Fdots) (dt := dt)
    (etaFs := etaFs) (Θdots := Θdots) (ws := ws) (sft := sft) (K := K)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hQd hYdotC hangC hEF hrest hstart

/-! ### The rear is at rest when the front is -/

/-- **The selected rears do not move at a time at which the fronts do not
move.**  The normal velocity of the selected rears solves the inverse Jacobi
ODE `∂_xη = sec δ · η_F − η` and is periodic, the slices being closed curves; if
the front normal velocity vanishes at the time `t`, the maximum principle with
the bound `0` forces `η(t, ·) = 0`.  This is the hypothesis `hrest` of the
path-distance assemblies, which therefore need only be assumed on the front. -/
theorem frameNormal_eq_zero_of_front_rest
    {P0 kh : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Fdots Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF sf sft dt Θdot w Θdots ws : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hPl : ∀ t, P0 ≤ P t)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hδt : ∀ t s, HasDerivAt (fun r => δ r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    (hetaFdef : ∀ t s, etaF t s = frontNormalVelocityAt Fdot Θ δ t s)
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
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (t : ℝ) (hfront : ∀ s, etaF t s = 0) :
    (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0 := by
  have hle12 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have hFC : ContDiff ℝ 1 (uncurry F) := by simpa using hFc2.of_le hle12
  have hΘC : ContDiff ℝ 1 (uncurry Θ) := by simpa using hΘc2.of_le hle12
  have hδC : ContDiff ℝ 1 (uncurry δ) := by simpa using hδc2.of_le hle12
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hQpos : ∀ t, 0 < rearArclength (δ t) (P t) := fun t =>
    SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl t)) hkh0 hkh1 (hδslice t)
      (hstrip0 t) (hstrip1 t)
  have hGC : ContDiff ℝ (1 : ℕ) (uncurry (frontParamTrack F Θ δ)) := by
    simpa [frontParamTrack] using contDiff_one_rearTrackFamily hFC hΘC hδC
  have hGx : ∀ t s, HasDerivAt (frontParamTrack F Θ δ t)
      ((Real.cos (δ t s) : ℂ) * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))) s :=
    fun t s => hasDerivAt_rearTrack (F := F t) (Θ := Θ t) (δ := δ t) (K := K t)
      (hF t s) (hΘ t s) (hsteer t s)
  have hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s)
      (trackVelocity Fdot Θdot w Θ δ t s) t :=
    fun t s => hasDerivAt_frontParamTrack_time hFa hΘa hδa t s
  have hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t := by
    intro t x
    have h := hasDerivAt_rearOwn_time (Gdot := trackVelocity Fdot Θdot w Θ δ) (sft := sft)
      hGC hGx hGt hsft t x
    rw [hYdot t x]
    exact h
  have hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x := by
    intro t x
    have h := hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence (K := K)
      (Fdot := Fdot) (Θdot := Θdot) (w := w) (Fdots := Fdots) (Θdots := Θdots) (ws := ws)
      (sft := sft) (Ydot := Ydot)
      hF hΘ hsteer hsfspace hcos hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot t x
    rwa [← hetaFdef t (sf t x)] at h
  have hsfC : ContDiff ℝ 1 (uncurry sf) :=
    SelectedChangeOfVariable.contDiff_one_sf hkh0 hkh1 hδcont hδt hdtc hstrip0 hstrip1 hsfinv
  have hYC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwn F Θ δ sf)) :=
    contDiff_one_rearOwn hFC hΘC hδC hsfC
  have hYx : ∀ t x, HasDerivAt (rearOwn F Θ δ sf t) (rearOwnTangent Θ δ sf t x) x :=
    hasDerivAt_rearOwn_space hF hΘ hsteer hsfspace hcos
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwn F Θ δ sf t x :=
    rearOwn_closing (kap := kh) (P := P) hkh0 hkh1 hδslice hstrip0 hstrip1 hdper hsfinv
      hFper hΘper
  have hYtframe : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ) * rearOwnTangent Θ δ sf t x
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * rearOwnTangent Θ δ sf t x)) t := by
    intro t x
    have hrec : ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
        + Complex.I * (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ))
        * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)) = Ydot t x :=
      frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    have heq : (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * rearOwnTangent Θ δ sf t x
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * rearOwnTangent Θ δ sf t x) = Ydot t x := by
      rw [← hrec]
      simp only [rearOwnTangent]
      ring
    rw [heq]
    exact hYt t x
  have htau0 : ∀ t x, rearOwnTangent Θ δ sf t x ≠ 0 := by
    intro t x h
    have hn := norm_rearOwn_tangent (Θ := Θ) (δ := δ) (sf := sf) t x
    rw [h] at hn
    simp at hn
  have hangshift : ∀ t x, rearOwnAngle Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwnAngle Θ δ sf t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift (kh := kh) (P := P) hkh0 hkh1 hδslice hstrip0
      hstrip1 hdper hsfinv hΘper t x
  have htauper : ∀ t, Function.Periodic (rearOwnTangent Θ δ sf t)
      (rearArclength (δ t) (P t)) := by
    intro t x
    have h2pi : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    simp only [rearOwnTangent, hangshift t x]
    push_cast
    rw [show Complex.I * ((rearOwnAngle Θ δ sf t x : ℂ) + 2 * (Real.pi : ℂ))
        = Complex.I * (rearOwnAngle Θ δ sf t x : ℂ) + Complex.I * ((2 * Real.pi : ℝ) : ℂ) by
      push_cast; ring, Complex.exp_add, h2pi, mul_one]
  have hetaper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) := by
    intro t x
    exact (GaugeClosingRelations.closing_relations hYC hYx hYtframe htau0 htauper hclose
      hQd t x).2
  funext x
  have hzero : |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ 0 := by
    refine abs_le_of_periodic_ode (hQpos t) (hetaper t) (hjac t) (fun y => ?_) x
    rw [hfront (sf t y)]
    simp
  exact abs_nonpos_iff.mp hzero

/-! ### Every hypothesis on the front -/

/-- **The path pseudodistance of the selected rears, with every hypothesis on
the front.**

This is `pathDist_le_of_front_regularity` with its last hypothesis about the
rear side removed as well: instead of asking the selected rears to be at rest
outside the time window of the path, it asks the *fronts* to be, which by
`frameNormal_eq_zero_of_front_rest` is enough.  What is left is the geometry and
the regularity of the front data — the two-sided bounds `P₀ ≤ P ≤ P₁` for the
front period, the selected strip `0 ≤ δ ≤ arcsin κ̂` with `|K| ≤ κ̂`, the closing
relations, the joint `C⁴` regularity of `F`, `Θ`, `δ`, the sup bound `E_F` on
the front normal velocity and its vanishing outside the window — together with
the equations defining the change of variable `sf` and the velocity `Ẏ`. -/
theorem pathDist_le_of_front_data {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh EF : ℝ} {P Qf' : ℝ → ℝ}
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
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hEF : ∀ t s, |etaF t s| ≤ EF)
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s, etaF t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hle24 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (2 : ℕ) ≤ 4)
  have hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0 := fun t ht =>
    frameNormal_eq_zero_of_front_rest (K := K) (Fdots := Fdots) (Θdots := Θdots) (ws := ws)
      (dt := dt) (sft := sft) (Qf' := Qf')
      hP0 hkh0 hkh1 hPl hF hΘ hsteer hstrip0 hstrip1 hdper hFper hΘper hδt hdtc hetaFdef
      hsfinv hsft hFa hΘa hδa hFdots hΘdots hws (hFc4.of_le hle24) (hΘc4.of_le hle24)
      (hδc4.of_le hle24) hYdot hQd t (hFrest t ht)
  exact pathDist_le_of_front_regularity Γ p' (Qf' := Qf') (Fdots := Fdots) (dt := dt)
    (etaFs := etaFs) (Θdots := Θdots) (ws := ws) (sft := sft) (K := K)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc4 hΘc4 hδc4 hYdot hQd hEF hrest hstart

/-! ### The Lipschitz form -/

/-- **The Lipschitz bound for a map of marked curves, with the constant read off
the front.**

`RearOwnPathDistFrameBounds.pathDist_le_mul_of_unitTime_costs` turns a bound
valid on every normal path of duration one into a bound by the pseudodistance.
Here the constant is the one produced by the geometry: the two gauge constants
are those of `pathDist_le_of_front_data`, built from the curvature ceiling `κ̂`
and the sup bound `E_F` on the normal velocity of the fronts. -/
theorem pathDist_le_of_front_unitTime_geometric {Fmap : Data → Data} {p q : Data}
    {P0 P1 kh EF Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQ : 0 < Q) (hEF : 0 ≤ EF)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 →
      pathDist (Fmap p) (Fmap q) ≤ gaugeJacobiConst P0 P1 kh
          (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
          ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
              * (kh / Real.sqrt (1 - kh ^ 2))
            + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) 1 Q
        * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (Fmap p) (Fmap q) ≤ gaugeJacobiConst P0 P1 kh
        (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
        ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
            * (kh / Real.sqrt (1 - kh ^ 2))
          + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) 1 Q
      * pathDist p q := by
  have hsq : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hrB : 0 ≤ (EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
      * (kh / Real.sqrt (1 - kh ^ 2))
    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := by positivity
  exact pathDist_le_of_front_unitTime hP0 hP1 hkh0 hkh1 hQ hrB h hne

end RearOwnPathDistSmooth
