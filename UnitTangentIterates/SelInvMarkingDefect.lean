import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnTerminal
import UnitTangentIterates.SelectedInverseRearOwnTerminalSpeed
import UnitTangentIterates.MarkingDeviation

/-!
# The terminal marking defect in the bound for the marked selected inverses

`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal` bounds
the path pseudodistance from `selInv κ̂ p` to the marked selected inverse of the
terminal curve of the path **read in the gauge marking** `Φ_T`.  The gauge
marking is a normalized parameter of the terminal slice, but need not be the
affine marking `u ↦ perim (selInv κ̂ q)·u`, and this is the last obstruction
between that bound and a comparison of the two marked selected inverses
themselves.

`SelectedInverseRearOwnShift.lean` removes the reparametrization by rigidity,
at the price of assuming the terminal datum to be a *member of the tube* — that
is, to be carried in a constant-speed parameter, which the gauge marking need
not provide.  This file takes the complementary route and *measures* the
defect: the elementary estimates of `MarkingDeviation.lean` turn a bound

```
  |Φ_T u − perim (selInv κ̂ q)·u| ≤ ε      (all u)
```

for the deviation of the gauge marking from the affine one into a uniform
bound for the difference of the two marked selected inverses,

```
  ‖(selInv κ̂ q).1 u − (selInv κ̂ p).1 u‖ ≤ gaugeJacobiConst … · cost Γ + ε ,
```

with **no hypothesis on the parametrization of the terminal datum**: only its
curve enters.  In particular, for a path along which the gauge marking stays
affine (`ε = 0`) the two marked selected inverses are uniformly within the
gauge constant times the cost of the path.

As `pathDist` is an infimum over a possibly empty set of costs, the existence
of a normal path joining `selInv κ̂ p` to the terminal datum is carried as an
explicit hypothesis, as in `PathMetric.norm_sub_le_pathDist`.

Main results: `sup_selInv_le_of_marking_defect` and, with the constant
produced by the cost density of the path instead of by compactness,
`sup_selInv_le_of_marking_defect_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvMarkingDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The two marked selected inverses of the ends of a normal path are
uniformly close, up to the defect of the gauge marking.**

Under the hypotheses of
`SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal`, if the
gauge marking of the terminal slice deviates from the affine marking of
`selInv κ̂ q` by at most `ε`, then the curves of the two marked selected
inverses differ by at most `gaugeJacobiConst … · cost Γ + ε` at every
parameter.  Nothing is assumed about the parametrization of the terminal datum
`q'`; it enters only through its curve and through the existence of a normal
path reaching it. -/
theorem sup_selInv_le_of_marking_defect {p q : Data} (Γ : NormalPath p q)
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
          ∀ (q' : Data) (eps : ℝ),
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ u, |Phi Γ.T u - perim (SelectedInverseMap.selInv kh q) * u| ≤ eps) →
            Nonempty (NormalPath (SelectedInverseMap.selInv kh p) q') →
            ∀ u, ‖(SelectedInverseMap.selInv kh q).1 u - (SelectedInverseMap.selInv kh p).1 u‖
              ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ + eps := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hPhi⟩ :=
    SelectedInverseRearOwnTerminal.exists_marked_rearOwn_pathDist_terminal Γ hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper
      hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv
  -- the perimeter of the marked selected inverse of the terminal curve is positive
  obtain ⟨-, hdodeT, hdmemT⟩ :=
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta
      hKeq hsol hstrip hdnper
  have hdcT : Continuous (δ Γ.T) :=
    Differentiable.continuous fun s => (hdodeT s).differentiableAt
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]
    exact SelectedInverseUnique.rearArclength_pos (hPpos Γ.T) hkh0 hkh1 hdcT hdmemT
  -- the marked selected inverse of the terminal curve is a member of the tube
  obtain ⟨dR', hdR'pos, hmemR, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, ?_⟩
  intro q' eps hq' hdev hne u
  exact MarkingDeviation.norm_sub_le_pathDist_add_marking hLpos hmemR.hasDerivAt_curve
    (fun x => norm_vel_eq_perim hmemR x) hq' hdev hne (hPhi q' hq') u


/-- **The same bound with the constant produced by the cost density of the
path.**

`SelectedInverseRearOwnTerminalSpeed.exists_marked_rearOwn_pathDist_terminal_speed`
replaces the sup bound of the front normal velocity, which the compactness
argument of the assembly produces and about which nothing is then known, by any
bound `M` for the cost density of the path.  This is the corresponding form of
`sup_selInv_le_of_marking_defect`. -/
theorem sup_selInv_le_of_marking_defect_speed {p q : Data} (Γ : NormalPath p q)
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
        ∀ (q' : Data) (eps : ℝ),
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv kh q).1
                (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          (∀ u, |Phi Γ.T u - perim (SelectedInverseMap.selInv kh q) * u| ≤ eps) →
          Nonempty (NormalPath (SelectedInverseMap.selInv kh p) q') →
          ∀ u, ‖(SelectedInverseMap.selInv kh q).1 u - (SelectedInverseMap.selInv kh p).1 u‖
            ≤ gaugeJacobiConst P0 P1 kh
                (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ + eps := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, Phi, hPhi0, hbase, hPhi⟩ :=
    SelectedInverseRearOwnTerminalSpeed.exists_marked_rearOwn_pathDist_terminal_speed Γ
      (M := M) hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper
      hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv hm
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
  refine ⟨hperimp, hperimq, Phi, hPhi0, hbase, ?_⟩
  intro q' eps hq' hdev hne u
  exact MarkingDeviation.norm_sub_le_pathDist_add_marking hLpos hmemR.hasDerivAt_curve
    (fun x => norm_vel_eq_perim hmemR x) hq' hdev hne (hPhi q' hq') u

end SelInvMarkingDefect
