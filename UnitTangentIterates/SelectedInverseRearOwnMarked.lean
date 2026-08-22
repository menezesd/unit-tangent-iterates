import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnShift
import UnitTangentIterates.RearOwnPathDistSteering

/-!
# The marked path-distance bound, when the front's marked point is at rest

`SelectedInverseRearOwnShift.exists_marked_rearOwn_pathDist_shift` identifies
the terminal curve of the path-distance bound with the marked selected inverse
`selInv κ̂ q` of the terminal curve of the path, *up to a shift of the marking*:
the gauge marking `Phi Γ.T` carries the normalized parameter of `selInv κ̂ q` to
the parameter of the terminal datum, and the rigidity of the marking makes that
change of parameter the shift by `Phi Γ.T 0 / perim (selInv κ̂ q)`.

The shift therefore vanishes exactly when the gauge marking fixes the base
point, `Phi Γ.T 0 = 0`.  That is no longer assumed: the gauge flow line through
a zero of the rate field stays there (`GaugeBaseFlow`), and the rate of the
selected rears at the marked point is the base drift of the front
(`RearBaseDrift`), so the base point of the gauge marking is fixed as soon as
the *front's* marked point is at rest along the path, `∀ t, Γ.eta t 0 = 0`.
Under that purely geometric hypothesis on the path the terminal datum *is*
`selInv κ̂ q`, and the bound is a bound for the **marked** path pseudodistance:

```
  pathDist (selInv κ̂ p) (selInv κ̂ q) ≤ gaugeJacobiConst … · cost Γ ,
```

not merely for the pseudodistance taken modulo the marking.

Main results: `pathDist_selInv_le_of_marking_fixed` and, with the selected
steering data produced from the curvature of the fronts as in
`RearOwnPathDistSteering.lean`, `exists_steering_pathDist_selInv_le`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnMarked

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  SelectedInverseRearOwnShift

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The marked path-distance bound for the two selected inverses, when the
front's marked point is at rest.**  Under the hypotheses of
`SelectedInverseRearOwnShift.exists_marked_rearOwn_pathDist_shift`, if the
terminal datum of the shadowing scheme is a member of the tube and the normal
velocity of the fronts vanishes at the marked point, `∀ t, Γ.eta t 0 = 0`, then
the gauge marking fixes the base point, that datum *is* the marked selected
inverse `selInv κ̂ q`, and the marked path pseudodistance from `selInv κ̂ p` to it
is at most the gauge constant times the cost of `Γ`. -/
theorem pathDist_selInv_le_of_marking_fixed {p q : Data} (Γ : NormalPath p q)
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
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
        (angleOfPath V A P) δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
          0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
          (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv kh q).1
                (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          (∀ t, Γ.eta t 0 = 0) →
          pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
            ≤ gaugeJacobiConst P0 P1 kh
                (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hPhi⟩ :=
    SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal Γ hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper
      hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv
  refine ⟨EF, hEF0, hEFbd, Phi, hPhi0, ?_⟩
  intro q' dPhi cq' kq' dq' hcq' hkq' hdq' hq' hdiff hcomp hrest
  -- the front's marked point is at rest, so the gauge marking fixes the base point
  have hmark : Phi Γ.T 0 = 0 := hbase hrest Γ.T
  -- the perimeter of the marked selected inverse of the terminal curve is positive
  obtain ⟨-, hdodeT, hdmemT⟩ :=
    delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta hKeq hsol hstrip hdnper
  have hdcT : Continuous (δ Γ.T) :=
    Differentiable.continuous fun s => (hdodeT s).differentiableAt
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]
    exact SelectedInverseUnique.rearArclength_pos (hPpos Γ.T) hkh0 hkh1 hdcT hdmemT
  have hkminq1 : kminq < 1 := by
    have h1 := hq.curv_lb 0
    have h2 := hubq 0
    have h3 : 0 < ‖q.2.1 0‖ ^ 3 := by
      have : 0 < ‖q.2.1 0‖ := lt_of_lt_of_le hcq (hq.speed_lb 0)
      positivity
    nlinarith
  have hkR : 0 < kminq / Real.sqrt (1 - kminq ^ 2) :=
    div_pos hkminq (Real.sqrt_pos.mpr (by nlinarith))
  obtain ⟨dR', hdR'pos, hmemR, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  have hshift := MarkedReparamRigidity.exists_shift_of_reparam hLpos hkR hdR'pos hcq' hkq' hdq'
    hmemR hq' (dpsi := fun u => dPhi u / perim (SelectedInverseMap.selInv kh q))
    (fun u => (hdiff u).div_const _) hcomp
  have hzero : Phi Γ.T 0 / perim (SelectedInverseMap.selInv kh q) = 0 := by
    rw [hmark, zero_div]
  rw [hzero] at hshift
  have hq'eq : q' = SelectedInverseMap.selInv kh q := by
    have h : q' = MarkedShift.shiftData 0 (SelectedInverseMap.selInv kh q) :=
      MarkedShift.eq_shiftData_of_curve hmemR hq' (by simpa using hshift)
    simpa using h
  rw [← hq'eq]
  exact hPhi q' hcomp


/-- **The marked path-distance bound with the steering data produced.**  The
selected steering angle, its arclength form and the change of variable from the
rear to the front arclength are built from the curvature of the fronts alone,
as in `RearOwnPathDistSteering.lean`; if in addition the front's marked point is
at rest along the path, the marked path pseudodistance of the two marked
selected inverses is at most the gauge constant times the cost of the path. -/
theorem exists_steering_pathDist_selInv_le {p q : Data} (Γ : NormalPath p q)
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
          ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
            0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
            (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ t, Γ.eta t 0 = 0) →
            pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
              ≤ gaugeJacobiConst P0 P1 kh
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
  exact pathDist_selInv_le_of_marking_fixed Γ hc hkmin hp hub hinjR hcq
    hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper
    hturn hnu (fun _ _ => rfl) hKeq hsol hstrip hdnper hKnper hKdnper
    (fun t σ => abs_le.mpr ⟨by linarith [hKn0 t σ, hKnk t σ], hKnk t σ⟩)
    hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsf

end SelectedInverseRearOwnMarked
