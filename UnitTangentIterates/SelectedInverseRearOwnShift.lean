import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnTerminal
import UnitTangentIterates.MarkedReparamRigidity
import UnitTangentIterates.MarkedShift

/-!
# The terminal end of the path bound is the marked selected inverse, up to a shift

`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal` shows
that the terminal curve of the normalized path-distance bound is the marked
selected inverse `selInv κ̂ q` of the terminal curve `q` of the path,
reparametrized by the gauge marking `u ↦ Phi Γ.T u / perim (selInv κ̂ q)`.

This file removes the reparametrization.  The gauge marking is *a priori* only
a normalized parameter; but the terminal datum of the shadowing scheme is
required to be a member of the tube, hence carried in the parameter in which
the speed is constant, and `MarkedReparamRigidity.exists_shift_of_reparam`
shows that two members of the tube tracing one another can differ only by a
shift of the marking.  Therefore

```
  q'.1 u = (selInv κ̂ q).1 (u + b)
```

for a constant `b`: the terminal curve of the bound *is* the marked selected
inverse of the terminal curve of the path, marked at another point.  The
differentiability of the gauge marking at the final time is carried as an
explicit hypothesis, as is done throughout this project for facts about the
gauge flow that the assembly does not produce.

Main result: `exists_marked_rearOwn_pathDist_shift`.  What remains for the
non-expansiveness of the selected inverse for the marked geometric metric is
that the shift `b` vanish, that is, that the gauge marking carry the base point
of `selInv κ̂ p` to that of `selInv κ̂ q`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnShift

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path-distance bound with the terminal curve identified up to a shift
of the marking.**

Under the hypotheses of
`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal`, any
*member of the tube* whose curve is the terminal curve of the bound — the
marked selected inverse `selInv κ̂ q` of the terminal curve of the path,
reparametrized by the gauge marking — is `selInv κ̂ q` itself with its marking
shifted by a constant, and the path pseudodistance from `selInv κ̂ p` to it is
at most the gauge constant times the cost of `Γ`. -/
theorem exists_marked_rearOwn_pathDist_shift {p q : Data} (Γ : NormalPath p q)
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
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
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
            (∃ b : ℝ, ∀ u, q'.1 u = (SelectedInverseMap.selInv kh q).1 (u + b)) ∧
              pathDist (SelectedInverseMap.selInv kh p) q' ≤ gaugeJacobiConst P0 P1 kh
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
  -- the perimeter of the marked selected inverse of the terminal curve is positive
  obtain ⟨-, hdodeT, hdmemT⟩ :=
    delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta hKeq hsol hstrip hdnper
  have hdcT : Continuous (δ Γ.T) :=
    Differentiable.continuous fun s => (hdodeT s).differentiableAt
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]
    exact SelectedInverseUnique.rearArclength_pos (hPpos Γ.T) hkh0 hkh1 hdcT hdmemT
  -- the marked selected inverse of the terminal curve is a member of the tube
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
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, ?_⟩
  intro q' dPhi cq' kq' dq' hcq' hkq' hdq' hq' hdiff hcomp
  refine ⟨?_, hPhi q' hcomp⟩
  refine ⟨Phi Γ.T 0 / perim (SelectedInverseMap.selInv kh q), ?_⟩
  refine MarkedReparamRigidity.exists_shift_of_reparam hLpos hkR hdR'pos hcq' hkq' hdq'
    hmemR hq' (dpsi := fun u => dPhi u / perim (SelectedInverseMap.selInv kh q))
    (fun u => (hdiff u).div_const _) hcomp

/-- **The marked selected inverses of the two ends of a normal path are close
modulo the marking.**

Combining the identification of the terminal end with the distance
`MarkedShift.pathDistShift` taken modulo the marking: the two marked selected
inverses `selInv κ̂ p` and `selInv κ̂ q` of the ends of the path are at distance
at most the gauge constant times the cost of `Γ`, once the marking of the
second is allowed to move.  The hypotheses on the terminal datum are those of
`exists_marked_rearOwn_pathDist_shift`; they are used only to produce one
shift. -/
theorem pathDistShift_selInv_le {p q : Data} (Γ : NormalPath p q)
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
  obtain ⟨-, -, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hPhi⟩ :=
    exists_marked_rearOwn_pathDist_shift Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq
      hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hdelta hKeq
      hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor
      hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv
  refine ⟨EF, hEF0, hEFbd, Phi, hPhi0, hbase, ?_⟩
  intro q' dPhi cq' kq' dq' hcq' hkq' hdq' hq' hdiff hcomp
  obtain ⟨⟨b, hb⟩, hbound⟩ := hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp
  obtain ⟨dR', hdR'pos, hmemR, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  have hqeq : q' = MarkedShift.shiftData b (SelectedInverseMap.selInv kh q) :=
    MarkedShift.eq_shiftData_of_curve hmemR hq' hb
  calc MarkedShift.pathDistShift (SelectedInverseMap.selInv kh p)
        (SelectedInverseMap.selInv kh q)
      ≤ pathDist (SelectedInverseMap.selInv kh p)
          (MarkedShift.shiftData b (SelectedInverseMap.selInv kh q)) :=
        MarkedShift.pathDistShift_le _ _ b
    _ ≤ _ := by rw [← hqeq]; exact hbound

end SelectedInverseRearOwnShift
