import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnShift
import UnitTangentIterates.RearOwnPathDistSteering

/-!
# The shift bound for the marked selected inverses, with the steering data produced

`SelectedInverseRearOwnShift.pathDistShift_selInv_le` bounds the distance
`MarkedShift.pathDistShift` between the marked selected inverses of the two ends
of a normal path of fronts, taken modulo the marking, by the gauge constant
times the cost of the path.  Among its hypotheses are the **selected steering
data**: the normalized steering angle `δ̂`, its arclength form `δ` and the
change of variable `sf` from the rear to the front arclength.

This file removes them.  Exactly as in
`RearOwnPathDistSteering.exists_steering_pathDist_le_of_path`, the normalized
steering angle is produced from the front curvature alone by
`RearOwnPathDistSteering.exists_normalized_steering` (a rescaled version of
`SteeringExistence.exists_periodic_steering`, one slice at a time), and the
change of variable by `ArclengthInverse.exists_inverse_rearArclength`.  What is
left is the tube membership of the two ends, the Umlaufsatz-type injectivity of
the rear tracks (carried as a hypothesis throughout this project), the pinching
`0 ≤ K̂ ≤ κ̂ < 1` of the curvature of the slices in the normalized parameter, and
the regularity of the period and of the curvature family in the path parameter.

Main result: `exists_steering_pathDistShift_selInv_le`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnShiftSteering

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn

variable {V A : ℝ → ℝ → ℂ} {Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the steering data produced.**

Under the tube hypotheses on the two ends of the path, the injectivity of the
rear tracks, the pinching `0 ≤ K̂ ≤ κ̂ < 1` of the curvature of the slices in the
normalized parameter and the regularity of the period and of the curvature
family, there are a normalized selected steering angle `δ̂`, its arclength form
`δ` and a change of variable `sf` from the rear to the front arclength for which
the conclusion of `SelectedInverseRearOwnShift.pathDistShift_selInv_le` holds:
the two marked selected inverses are at distance, modulo the marking, at most
the gauge constant times the cost of the path. -/
theorem exists_steering_pathDistShift_selInv_le {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq Md MP CK CP : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjRq : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ' dl) (Ico 0 (perim q)))
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
          ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
            0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
            (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            MarkedShift.pathDistShift (SelectedInverseMap.selInv kh p)
                (SelectedInverseMap.selInv kh q) ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hKnc : ∀ t, Continuous (Kn t) := fun t =>
    hKnC3.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨dn, hdnper, hstrip, hsol⟩ :=
    RearOwnPathDistSteering.exists_normalized_steering (P := P) hkh0 hkh1 hPpos hKnc
      hKnper hKn0 hKnk
  set δ : ℝ → ℝ → ℝ := fun t s => dn t (s / P t) with hδdef
  have hdnc : ∀ t, Continuous (dn t) := fun t =>
    Differentiable.continuous fun σ => (hsol t σ).differentiableAt
  have hδc : ∀ t, Continuous (δ t) := fun t =>
    (hdnc t).comp (continuous_id.div_const (P t))
  have hslice : ∀ t : ℝ, ∃ f : ℝ → ℝ, ∀ x, rearArclength (δ t) (f x) = x := fun t =>
    exists_inverse_rearArclength hkh0 hkh1 (hδc t) (fun s => (hstrip t _).1)
      (fun s => (hstrip t _).2)
  choose sf hsf using hslice
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, fun _ _ => rfl, hsf, ?_⟩
  exact SelectedInverseRearOwnShift.pathDistShift_selInv_le Γ hc hkmin hp hub hinjR hcq
    hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper
    hturn hnu (fun _ _ => rfl) hKeq hsol hstrip hdnper hKnper hKdnper
    (fun t σ => abs_le.mpr ⟨by linarith [hKn0 t σ, hKnk t σ], hKnk t σ⟩)
    hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsf

end SelectedInverseRearOwnShiftSteering
