import Mathlib
import UnitTangentIterates.RearOwnPathDistSmooth
import UnitTangentIterates.RearOwnPathDistGeometricDefectC2

/-!
# The path pseudodistance from the regularity of the front alone, together with
the C² defect of its gauge marking

The two assemblies of `RearOwnPathDistSmooth.lean` —
`pathDist_le_of_front_regularity`, which discharges the regularity hypotheses on
the rear side from the joint `C⁴` regularity of the front data, and
`pathDist_le_of_front_data`, which also replaces the resting condition on the
rears by the resting condition on the fronts — restated with the extra
conclusions of `RearOwnPathDistGeometricDefectC2.lean` about the gauge marking
`Φ` in which the pseudodistance is read: it fixes the base point, reads exactly
one rear period, deviates from the affine marking of the terminal period by at
most `2 P₁ κ̂/(1 − κ̂²) · cost Γ`, and leaves the terminal marked curve within
`markingC2Bound` of the marked reference curve `b` in the `C²` metric.

The only additional hypothesis is the vanishing of the base drift of the front.

Main results: `pathDist_and_distC2_le_of_front_regularity`,
`pathDist_and_distC2_le_of_front_data`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSmoothDefectC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  RearOwnPathDistFrameBounds RearOwnTangential RearOwnPathDistGeometric
  RearOwnHigherRegularity RearOwnPathDistSmooth MarkingDeviationC2 MarkingFlowDefectC2
  RearOwnTangentialCostC2

/-- **The path pseudodistance of the selected rears with every constant and every
regularity hypothesis read off the front, together with the defect of its gauge
marking.**  `RearOwnPathDistSmooth.pathDist_le_of_front_regularity` with the
extra conclusions about the marking. -/
theorem pathDist_and_distC2_le_of_front_regularity {p q : Data} (Γ : NormalPath p q) (p' b : Data)
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
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0)
    -- the terminal curve, a member of the tube tracing the terminal slice
    {cq kminq dltq kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b)
    (hperimb : perim b = rearArclength (δ Γ.T) (P Γ.T))
    (hevb : ∀ x, ev b x = rearOwn F Θ δ sf Γ.T x)
    (hevd : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (-frameTangential (partialTime (rearOwn F Θ δ sf)) (rearOwnAngle Θ δ sf) t
          (Phi t u)) t) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
      (∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
        dist q' b ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
          (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
          (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
            (gaugeGrowth2 kh * cost Γ))
          (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
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
  exact RearOwnPathDistGeometricDefectC2.pathDist_and_distC2_le_of_front_normalVelocity
    Γ p' b (Qf' := Qf') (Fdots := Fdots) (dt := dt)
    (etaFs := etaFs) (Θdots := Θdots) (ws := ws) (sft := sft) (K := K)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hQd hYdotC hangC hEF hrest hstart hdrift
    hcq hb hperimb hevb hevd hΘb hkbd hklip

/-! ### The rear is at rest when the front is -/

/-- **The path pseudodistance of the selected rears with every hypothesis on the
front, together with the C² defect of its gauge marking.**
`RearOwnPathDistSmooth.pathDist_le_of_front_data` with the extra
conclusions about the marking. -/
theorem pathDist_and_distC2_le_of_front_data {p q : Data} (Γ : NormalPath p q) (p' b : Data)
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
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0)
    -- the terminal curve, a member of the tube tracing the terminal slice
    {cq kminq dltq kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b)
    (hperimb : perim b = rearArclength (δ Γ.T) (P Γ.T))
    (hevb : ∀ x, ev b x = rearOwn F Θ δ sf Γ.T x)
    (hevd : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (-frameTangential (partialTime (rearOwn F Θ δ sf)) (rearOwnAngle Θ δ sf) t
          (Phi t u)) t) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
      (∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
        dist q' b ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
          (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
          (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
            (gaugeGrowth2 kh * cost Γ))
          (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
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
  exact pathDist_and_distC2_le_of_front_regularity Γ p' b (Qf' := Qf') (Fdots := Fdots) (dt := dt)
    (etaFs := etaFs) (Θdots := Θdots) (ws := ws) (sft := sft) (K := K)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc4 hΘc4 hδc4 hYdot hQd hEF hrest hstart hdrift
    hcq hb hperimb hevb hevd hΘb hkbd hklip

end RearOwnPathDistSmoothDefectC2
