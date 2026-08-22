import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnShift
import UnitTangentIterates.SelectedInverseRearOwnTerminalSpeed

/-!
# The terminal end of the path bound up to a shift, with the constant fixed by
the speed of the path

`SelectedInverseRearOwnShift.exists_marked_rearOwn_pathDist_shift` and
`SelectedInverseRearOwnShift.pathDistShift_selInv_le` state the path-distance
bound with the terminal curve identified up to a shift of the marking, but the
sup bound `E_F` of the front normal velocity occurring in their constant is
produced by compactness.

This file gives the same two statements with `E_F` supplied by a bound `M` for
the **cost density of the path**, as `SelectedInverseRearOwnTerminalSpeed.lean`
does one step below.  The constant is then a function of the tube constants, of
the duration of the path and of `M` alone; on a tube of curves this makes it
uniform, which is what a Lipschitz estimate for the selected inverse requires.

* `exists_marked_rearOwn_pathDist_shift_speed`;
* `pathDistShift_selInv_le_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnShiftSpeed

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  SelectedInverseRearOwnTerminalSpeed

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path-distance bound with the terminal curve identified up to a shift
of the marking, with the front normal velocity bounded by the cost density of
the path.**

Same statement as
`SelectedInverseRearOwnShift.exists_marked_rearOwn_pathDist_shift`, with the
sup bound `E_F` of the front normal velocity replaced by any bound `M` for the
cost density of the path. -/
theorem exists_marked_rearOwn_pathDist_shift_speed {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M Md MP CK CP : ℝ}
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
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hm : ∀ t, Γ.m t ≤ M) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
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
                (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, Phi, hPhi0, hbase, hPhi⟩ :=
    SelectedInverseRearOwnTerminalSpeed.exists_marked_rearOwn_pathDist_terminal_speed Γ
      (M := M) hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper
      hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv hm
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
  refine ⟨hperimp, hperimq, Phi, hPhi0, hbase, ?_⟩
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
`exists_marked_rearOwn_pathDist_shift_speed`; they are used only to produce one
shift.  Same statement as
`SelectedInverseRearOwnShift.pathDistShift_selInv_le`, with the sup bound `E_F`
of the front normal velocity replaced by any bound `M` for the cost density of
the path. -/
theorem pathDistShift_selInv_le_speed {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M Md MP CK CP : ℝ}
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
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hm : ∀ t, Γ.m t ≤ M) :
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
              (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  obtain ⟨-, -, Phi, hPhi0, hbase, hPhi⟩ :=
    exists_marked_rearOwn_pathDist_shift_speed Γ (M := M)
      hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq
      hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hdelta hKeq
      hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor
      hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv hm
  refine ⟨Phi, hPhi0, hbase, ?_⟩
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

end SelectedInverseRearOwnShiftSpeed
