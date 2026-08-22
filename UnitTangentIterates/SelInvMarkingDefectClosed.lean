import Mathlib
import UnitTangentIterates.SelInvMarkingDefect
import UnitTangentIterates.SelectedInverseRearOwnTerminalDefect

/-!
# The two marked selected inverses are uniformly close, with no residual defect

`SelInvMarkingDefect.sup_selInv_le_of_marking_defect` bounds the difference of
the two marked selected inverses of the ends of a normal path by
`gaugeJacobiConst … · cost Γ + ε`, where `ε` is *any* bound for the deviation of
the gauge marking of the terminal slice from the affine marking.  Nothing there
produces such an `ε`.

`SelectedInverseRearOwnTerminalDefect.exists_marked_rearOwn_pathDist_and_defect_terminal`
produces one: for a path that does not move at its marked point, the gauge
marking deviates from the affine one by at most `2 P₁ κ̂/(1 − κ̂²) · cost Γ`.
Combining the two closes the loop and yields an unconditional bound

```
  ‖(selInv κ̂ q).1 u − (selInv κ̂ p).1 u‖
      ≤ (gaugeJacobiConst … + 2 P₁ κ̂/(1 − κ̂²)) · cost Γ ,
```

proportional to the cost of the path alone.

Main result: `sup_selInv_le_of_marking_defect_cost`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvMarkingDefectClosed

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The two marked selected inverses of the ends of a normal path are
uniformly close, by a multiple of the cost of the path.**

The combination of `SelInvMarkingDefect.sup_selInv_le_of_marking_defect` with the
marking defect bound of
`SelectedInverseRearOwnTerminalDefect.exists_marked_rearOwn_pathDist_and_defect_terminal`:
for a normal path that does not move at its marked point, the two marked
selected inverses differ, at every parameter, by at most
`(gaugeJacobiConst … + 2 P₁ κ̂/(1 − κ̂²)) · cost Γ`. -/
theorem sup_selInv_le_of_marking_defect_cost {p q : Data} (Γ : NormalPath p q)
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
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          (∀ t, Phi t 0 = 0) ∧
          ∀ q' : Data,
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            Nonempty (NormalPath (SelectedInverseMap.selInv kh p) q') →
            ∀ u, ‖(SelectedInverseMap.selInv kh q).1 u - (SelectedInverseMap.selInv kh p).1 u‖
              ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                  (rearArclength (δ 0) (P 0)) * cost Γ
                + 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hdefect, hPhi⟩ :=
    SelectedInverseRearOwnTerminalDefect.exists_marked_rearOwn_pathDist_and_defect_terminal Γ
      hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
      hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
      hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
      hFc4 hΘc4 hsfinv hmark
  obtain ⟨-, hdodeT, hdmemT⟩ :=
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta
      hKeq hsol hstrip hdnper
  have hdcT : Continuous (δ Γ.T) :=
    Differentiable.continuous fun s => (hdodeT s).differentiableAt
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]
    exact SelectedInverseUnique.rearArclength_pos (hPpos Γ.T) hkh0 hkh1 hdcT hdmemT
  obtain ⟨dR', hdR'pos, hmemR, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, ?_⟩
  intro q' hq' hne u
  exact MarkingDeviation.norm_sub_le_pathDist_add_marking hLpos hmemR.hasDerivAt_curve
    (fun x => norm_vel_eq_perim hmemR x) hq' hdefect hne (hPhi q' hq') u

end SelInvMarkingDefectClosed
