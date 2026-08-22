import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnTerminal
import UnitTangentIterates.SelectedInverseRearOwnPathDefectC2

/-!
# The path-distance bound between the two marked selected inverses, together with
the C² defect of the gauge marking of the terminal end

`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal`
identifies the terminal curve of the bound with the marked selected inverse
`selInv κ̂ q` reparametrized by the gauge marking
`u ↦ Φ_T(u) / perim (selInv κ̂ q)`, and observes that what is still missing for
non-expansiveness is that this reparametrization be the identity.

This file measures how far it is from the identity: under the geometric
hypothesis that the path does not move at its marked point, the gauge marking
fixes the base point and

`|Φ_T(u) − perim (selInv κ̂ q)·u| ≤ 2 P₁ κ̂/(1 − κ̂²) · cost Γ`

for every `u`, so the reparametrization is the identity up to an error
proportional to the cost of the path.  It also carries the `C²` form of that
statement: in the metric of the space of marked curves, the terminal marked
curve read through the gauge is within `markingC2Bound …` of the terminal marked
selected inverse `selInv κ̂ q` itself.

Main result: `exists_marked_rearOwn_pathDist_and_distC2_terminal`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnTerminalDefectC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2

variable {X V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path-distance bound between the two marked selected inverses, with the
C² defect of the gauge marking of the terminal end.**
`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal` with the
gauge marking known to fix the base point and to deviate from the affine marking
`u ↦ perim (selInv κ̂ q)·u` of the terminal marked selected inverse by at most
`2 P₁ κ̂/(1 − κ̂²) · cost Γ`, and with the terminal marked curve read through the
gauge within `markingC2Bound …` of `selInv κ̂ q` in the `C²` metric. -/
theorem exists_marked_rearOwn_pathDist_and_distC2_terminal {p q : Data} (Γ : NormalPath p q)
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
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the tangent-angle lift of the terminal marked selected inverse
    {kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hevd : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          (∀ t, Phi t 0 = 0) ∧
          (∀ u t, HasDerivAt (fun r => Phi r u)
            (-frameTangential (partialTime (rearOwn (frontOfPath Γ.X P)
                (angleOfPath V A P) δ sf))
              (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t) ∧
          (∀ u, |Phi Γ.T u - perim (SelectedInverseMap.selInv kh q) * u|
            ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
          (∀ q' : Data, (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) →
            (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
            dist q' (SelectedInverseMap.selInv kh q) ≤ markingC2Bound
              (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
              (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
              (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
                (gaugeGrowth2 kh * cost Γ))
              (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
          ∀ q' : Data, (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            pathDist (SelectedInverseMap.selInv kh p) q' ≤ gaugeJacobiConst P0 P1 kh
                (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  -- the terminal slice and its marked selected inverse
  obtain ⟨hdperT, hdodeT, hdmemT⟩ :=
    delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta hKeq hsol hstrip hdnper
  obtain ⟨-, -, hperimq, hevq⟩ :=
    ev_selInv_eq_rearOwn (X := Γ.X) (V := V) (A := A) (P := P) (δ := δ) (sf := sf)
      hcq hkminq hkh1 hq hubq hinjRq (hPpos Γ.T) (hV Γ.T) (hA Γ.T) (hAcont Γ.T)
      (hspeed Γ.T) (funext Γ.finish) hdperT hdodeT hdmemT (hsfinv Γ.T)
  have hdcT : Continuous (δ Γ.T) :=
    Differentiable.continuous fun s => (hdodeT s).differentiableAt
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]
    exact SelectedInverseUnique.rearArclength_pos (hPpos Γ.T) hkh0 hkh1 hdcT hdmemT
  obtain ⟨dR', -, hmemR, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  -- the bound with the initial end identified, the terminal marked selected inverse
  -- playing the role of the reference curve of the `C²` comparison
  obtain ⟨-, -, -, hperimp, -, -, EF, hEF0, hEFbd, Phi, hPhi0, hbase, -, hflow, hdefect,
      hdistC2, hPhi⟩ :=
    SelectedInverseRearOwnPathDefectC2.exists_marked_rearOwn_pathDist_and_distC2 Γ
      (SelectedInverseMap.selInv kh q)
      hc hkmin hp hub hinjR hP0
      hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol
      hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK
      hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv hmark
      hLpos hmemR hperimq hevq hevd hΘb hkbd hklip
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, fun u => by rw [hPhi0 u, hperimp],
    hbase, hflow, fun u => by rw [hperimq]; exact hdefect u, ?_, ?_⟩
  · intro q' hq' hd1 hd2
    refine hdistC2 q' (fun u => ?_) hd1 hd2
    rw [hq' u, ← hevq (Phi Γ.T u), ev]
  · intro q' hq'
    refine hPhi q' fun u => ?_
    rw [hq' u, ← hevq (Phi Γ.T u), ev]

end SelectedInverseRearOwnTerminalDefectC2
