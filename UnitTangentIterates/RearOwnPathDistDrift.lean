import Mathlib
import UnitTangentIterates.RearOwnPathDistDefect
import UnitTangentIterates.GaugePathRearFamilyDrift
import UnitTangentIterates.RearBaseDriftBound

/-!
# The path pseudodistance of the selected rears from the front data, with a drifting base point

`RearOwnPathDistDefect.pathDist_and_defect_le_of_front_family` expresses
`GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family` in terms of the
front data alone.  Both carry the gauge normalization `ξ(t,0) = 0`, which
`RearBaseDrift.lean` traces back to the marked point of the path of fronts being
at rest and `PinchedPathRigidity.lean` shows to be incompatible with motion.

This file is the same step applied to
`GaugePathRearFamilyDrift.pathDist_and_defect_le_of_rear_family_drift`: the
normalization is replaced by a window estimate for the tangential component,
`|x| ≤ L_max → |ξ(t,x)| ≤ Cx t ≤ rr·m t`, and the conclusion records that the
base point of the gauge marking drifts by at most `rr · cost Γ` instead of
staying put.

Main result: `pathDist_and_defect_le_of_front_family_drift`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistDrift

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugePathRearFamily GaugePathDistVariable GaugeGeometryPathVariable

/-- **The path pseudodistance of the selected rears of a path of fronts,
together with the defect of the gauge marking, with no hypothesis on the marked
point.**  Everything asked of the rears is a property of the *front* data, as in
`RearOwnPathDist.pathDist_le_of_front_family`; the gauge normalization is
replaced by the window estimate `|ξ(t,x)| ≤ Cx t ≤ rr·m t` for `|x| ≤ L_max`,
and the gauge marking is known to keep its base point within `rr · cost Γ` of
the origin, to read one rear period from wherever its base point is, and to
deviate from the affine marking of the terminal period by at most
`2 L_max κ · cost Γ + rr · cost Γ`. -/
theorem pathDist_and_defect_le_of_front_family_drift {p q : Data} (Γ : NormalPath p q)
    (p' : Data)
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
    -- the window estimate for the tangential component
    {Cx : ℝ → ℝ} {Lmax kappa rr : ℝ}
    (hxiW : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ Cx t) (hCxcont : Continuous Cx)
    (hxiR : ∀ t, Cx t ≤ rr * Γ.m t) (hrr : 0 ≤ rr)
    (hLmax0 : 0 < Lmax) (hsmall : rr * cost Γ < Lmax)
    (hQmax : ∀ t, rearArclength (δ t) (P t) + rr * cost Γ ≤ Lmax)
    (hcost : ∀ t, Cx t / Lmax ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ rr * cost Γ) ∧
      (∀ t, Phi t 1 = Phi t 0 + rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ + rr * cost Γ) ∧
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
  exact GaugePathRearFamilyDrift.pathDist_and_defect_le_of_rear_family_drift Γ p' D
    (Qf := fun t => rearArclength (δ t) (P t))
    (Qf' := Qf') (delta := δ) (K := K) (etaF := etaF) (etaFs := etaFs)
    (etaR := fun t x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) (sf := sf)
    (Y := rearOwn F Θ δ sf) (tauY := rearOwnTangent Θ δ sf)
    hP0 hkh0 hkh1 hPl hPu hsteer hstrip0 hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper
    hlink hsfinv hetaR hrest (fun _ => rfl) hQd hv1 hYC hYx hYt
    (fun t x => norm_rearOwn_tangent t x) hclose hstart hxiW hCxcont hxiR hrr hLmax0
    hsmall hQmax hcost

/-- **The same, with the window estimate discharged from the front data.**  For a
front that moves normally at its marked point — which is automatic along a
normal path, and is *not* the condition that the marked point be at rest — the
tangential component of the motion of the selected rears obeys
`|ξ(t,x)| ≤ (κ̂ + L_max·κ̂/(1−κ̂²))·m t` on the window `|x| ≤ L_max`
(`RearBaseDriftBound.abs_frameTangential_le_cost_on_window_free`).  So the drift
rate `rr` of the base point of the gauge marking is a function of the curvature
pinching and of the window alone. -/
theorem pathDist_and_defect_le_of_front_family_drift_auto {p q : Data}
    (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Gdot Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF etaFs sf sft dt Θdot w : ℝ → ℝ → ℝ}
    {vdot psidot xix etax : ℝ → ℝ → ℝ}
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
    (hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s) (Gdot t s) t)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hYdot : ∀ t x, Ydot t x = Gdot t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hR2 : ∀ t, ContDiff ℝ 2 (uncurry (rearFamily F Θ δ (sf t))))
    (hv : ∀ t x, HasDerivAt (fun a' => frameSpeed δ (sf t) t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => frameAngle Θ δ (sf t) a' x) (psidot t x) t)
    (hxi : ∀ t x, HasDerivAt
      (fun x' => frameTangential (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (xix t x) x)
    (heta : ∀ t x, HasDerivAt
      (fun x' => frameNormal (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (etax t x) x)
    (hv1 : ∀ t x, D.v t x = 1)
    (hxiD : ∀ t x, D.xi t x = frameTangential Ydot (rearOwnAngle Θ δ sf) t x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    -- the extra regularity, and the normal motion of the front at the marked point
    (hPC : ContDiff ℝ 1 P) (hYdotC : ContDiff ℝ 1 (uncurry Ydot))
    (hangC : ContDiff ℝ 1 (uncurry (rearOwnAngle Θ δ sf)))
    (hGsplit : ∀ t s, Gdot t s = trackVelocity Fdot Θdot w Θ δ t s)
    (hFdot : ∀ t, Fdot t 0
      = (etaF t 0 : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t 0 : ℂ))))
    {Lmax kappa : ℝ}
    (hLmax0 : 0 < Lmax)
    (hsmall : (kh + Lmax * (kh / (1 - kh ^ 2))) * cost Γ < Lmax)
    (hQmax : ∀ t, rearArclength (δ t) (P t)
      + (kh + Lmax * (kh / (1 - kh ^ 2))) * cost Γ ≤ Lmax)
    (hcost : ∀ t, (kh + Lmax * (kh / (1 - kh ^ 2))) * Γ.m t / Lmax ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t ∈ Icc (0:ℝ) Γ.T,
        |Phi t 0| ≤ (kh + Lmax * (kh / (1 - kh ^ 2))) * cost Γ) ∧
      (∀ t, Phi t 1 = Phi t 0 + rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ + (kh + Lmax * (kh / (1 - kh ^ 2))) * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hsfC : ContDiff ℝ 1 (uncurry sf) :=
    SelectedChangeOfVariable.contDiff_one_sf hkh0 hkh1 hδcont hδt hdtc hstrip0 hstrip1 hsfinv
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
  have hetaR : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x := by
    intro t x
    have h := hasDerivAt_rearOwn_normal_jacobi (F := F) (Θ := Θ) (δ := δ) (K := K)
      (sf := sf) (sft := sft) (Gdot := Gdot) (Fdot := Fdot)
      (vdot := vdot) (psidot := psidot) (xix := xix) (etax := etax)
      Ydot hF hΘ hsteer hsfspace hcos hGt hFa hR2 hv hpsia hxi heta hYdot t x
    rwa [hetaFdef t (sf t x)]
  -- the normal velocity of the front is dominated by the cost density of the path
  have hEF : ∀ t s, |etaF t s| ≤ Γ.m t := by
    intro t s
    have hPt : P t ≠ 0 := ne_of_gt (lt_of_lt_of_le hP0 (hPl t))
    have hid : P t * (s / P t) = s := by field_simp
    have h := hlink t (s / P t)
    rw [hid] at h
    rw [← h]
    exact Γ.abs_eta_le t _
  -- the rear period is positive
  have hQpos : ∀ t, 0 < rearArclength (δ t) (P t) := fun t =>
    SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl t)) hkh0 hkh1
      (hδslice t) (hstrip0 t) (hstrip1 t)
  -- the window estimate for the tangential component, with no hypothesis on the
  -- marked point of the path
  have hxiW : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ (kh + Lmax * (kh / (1 - kh ^ 2))) * Γ.m t := by
    intro t x hx
    rw [hxiD t x]
    exact RearBaseDriftBound.abs_frameTangential_le_cost_on_window_free
      (etaF := etaF) (Fdot := Fdot) (Θdot := Θdot) (w := w) (sft := sft) (m := Γ.m)
      hkh0 hkh1 hQpos hstrip0 hstrip1 hcos hF hΘ hsteer hsfspace hsfinv hdper hFper hΘper
      hFC hΘC hδC hsfC hPC hYd hYdotC hangC hetaR hEF Γ.m_nonneg hsft
      (fun t x => by rw [hYdot t x, hGsplit t (sf t x)]) hFdot t hx
  have hrr : (0:ℝ) ≤ kh + Lmax * (kh / (1 - kh ^ 2)) := by
    have hsq : 0 < 1 - kh ^ 2 := by nlinarith
    have : 0 ≤ kh / (1 - kh ^ 2) := by positivity
    nlinarith
  exact pathDist_and_defect_le_of_front_family_drift Γ p' D
    (Gdot := Gdot) (Fdot := Fdot) (Ydot := Ydot) (sft := sft) (dt := dt)
    (vdot := vdot) (psidot := psidot) (xix := xix) (etax := etax)
    (Cx := fun t => (kh + Lmax * (kh / (1 - kh ^ 2))) * Γ.m t)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft hGt hFa
    hYdot hR2 hv hpsia hxi heta hv1 hxiD hrest hQd hstart hxiW
    (continuous_const.mul Γ.cont_m) (fun t => le_rfl) hrr hLmax0 hsmall hQmax hcost

end RearOwnPathDistDrift
