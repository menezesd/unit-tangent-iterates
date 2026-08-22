import Mathlib
import UnitTangentIterates.RearOwnTangential

/-!
# The path pseudodistance of the selected rears, with the gauge constants read
off the geometry

`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds` carries two
prescribed constants `rL`, `rB` bounding the first two arclength derivatives of
the tangential component `ξ = ⟨Ẏ, e^{iΨ}⟩` of the motion of the selected rears.
They were the last data of that statement that the caller had to produce by
hand.

Here they are produced from the geometry.  By `RearOwnTangential.lean` the
family of rear tracks written in its own arclength has unit speed, so

`∂_xξ = η tan δ`,  `∂_x²ξ = (sec δ · η_F − η) tan δ + η (K − sin δ) sec³δ`,

and on the selected strip `0 ≤ δ ≤ arcsin κ̂`, `|K| ≤ κ̂` two sup bounds — `E₀`
for the normal velocity `η` of the selected rears and `E_F` for the normal
velocity `η_F` of the fronts — bound both.  The resulting statement,
`pathDist_le_of_front_geometric`, asks nothing of the tangential motion of the
rears: every hypothesis is on the front data, on the selected strip, or is the
sup bound `E₀` on the rear normal velocity, itself the quantity the inverse
Jacobi estimates control.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistGeometric

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  RearOwnPathDistFrameBounds RearOwnTangential

/-- **The path pseudodistance of the selected rears of a path of fronts, with
the two gauge constants supplied by the geometry.**

The hypotheses are those of
`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds`, except that the
two prescribed bounds on the arclength derivatives of the tangential component
of the motion are replaced by the sup bounds `E₀` on the normal velocity of the
selected rears and `E_F` on the normal velocity of the fronts.  The gauge
constants of the conclusion are the explicit

`rL = E₀ κ̂/√(1−κ̂²)`,
`rB = (E_F/√(1−κ̂²) + E₀) κ̂/√(1−κ̂²) + 2E₀ κ̂/(1−κ̂²)^{3/2}`. -/
theorem pathDist_le_of_front_geometric {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh E0 EF : ℝ} {P Qf' : ℝ → ℝ}
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
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    -- the two geometric sup bounds
    (hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0)
    (hEF : ∀ t s, |etaF t s| ≤ EF)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (E0 * (kh / Real.sqrt (1 - kh ^ 2)))
            ((EF / Real.sqrt (1 - kh ^ 2) + E0) * (kh / Real.sqrt (1 - kh ^ 2))
              + E0 * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  -- the motion of the family of rear tracks in its own arclength
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
  -- the inverse Jacobi ODE for the normal velocity of the family
  have hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x := by
    intro t x
    have h := hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence (K := K)
      (Fdot := Fdot) (Θdot := Θdot) (w := w) (Fdots := Fdots) (Θdots := Θdots) (ws := ws)
      (sft := sft) (Ydot := Ydot)
      hF hΘ hsteer hsfspace hcos hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot t x
    rwa [← hetaFdef t (sf t x)] at h
  -- the two gauge constants
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hYdotC2 : ContDiff ℝ (2 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hrL : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ E0 * (kh / Real.sqrt (1 - kh ^ 2)) := fun t x =>
    abs_partialX_frameTangential_le hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsfspace hcos
      hYt hYdotC1 hangC1 hE0 t x
  have hrB : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
        ≤ (EF / Real.sqrt (1 - kh ^ 2) + E0) * (kh / Real.sqrt (1 - kh ^ 2))
          + E0 * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := fun t x =>
    abs_partialX_partialX_frameTangential_le hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer
      hsfspace hcos hYt hYdotC2 hangC2 hjac hE0 hEF t x
  exact pathDist_le_of_front_frame_bounds Γ p' (Qf' := Qf') (Fdot := Fdot) (Fdots := Fdots)
    (Ydot := Ydot) (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt)
    (sft := sft) (K := K) (etaF := etaF) (etaFs := etaFs)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hQd hYdotC hangC hrL hrB hrest hstart

/-- **The path pseudodistance of the selected rears, with the gauge constants
read off the front alone.**

The sup bound `E₀` on the normal velocity of the selected rears is not assumed
here: the rear normal velocity solves the inverse Jacobi ODE and is periodic,
since the slices are closed curves, so the maximum principle
(`RearOwnTangential.abs_frameNormal_le_of_periodic`) bounds it by
`E_F/√(1−κ̂²)`.  Every constant of the conclusion is therefore produced by the
front data: the period bounds `P₀, P₁`, the curvature ceiling `κ̂`, and the sup
bound `E_F` on the normal velocity of the fronts. -/
theorem pathDist_le_of_front_normalVelocity {p q : Data} (Γ : NormalPath p q) (p' : Data)
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
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
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
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  -- the rear period is positive
  have hQpos : ∀ t, 0 < rearArclength (δ t) (P t) := fun t =>
    SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl t)) hkh0 hkh1 (hδslice t)
      (hstrip0 t) (hstrip1 t)
  -- the motion of the family in its own arclength
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
  -- the inverse Jacobi ODE
  have hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x := by
    intro t x
    have h := hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence (K := K)
      (Fdot := Fdot) (Θdot := Θdot) (w := w) (Fdots := Fdots) (Θdots := Θdots) (ws := ws)
      (sft := sft) (Ydot := Ydot)
      hF hΘ hsteer hsfspace hcos hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot t x
    rwa [← hetaFdef t (sf t x)] at h
  -- the normal velocity of the rears is periodic, by the closing relation
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
  -- the sup bound on the rear normal velocity, by the maximum principle
  have hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ EF / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_of_periodic hkh0 hkh1 hstrip0 hstrip1 hQpos hetaper hjac hEF t x
  exact pathDist_le_of_front_geometric Γ p' (Qf' := Qf') (Fdot := Fdot) (Fdots := Fdots)
    (Ydot := Ydot) (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt)
    (sft := sft) (K := K) (etaF := etaF) (etaFs := etaFs)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hQd hYdotC hangC hE0 hEF hrest hstart

end RearOwnPathDistGeometric
