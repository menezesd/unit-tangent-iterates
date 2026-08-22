import Mathlib
import UnitTangentIterates.SelInvMarkingDefect
import UnitTangentIterates.MarkingDefectCost

/-!
# The marking defect produced, and the bound purely in the cost of the path

`SelInvMarkingDefect.sup_selInv_le_of_marking_defect` bounds the uniform
distance of the two marked selected inverses of the ends of a normal path of
fronts by `gaugeJacobiConst … · cost Γ + ε`, where `ε` is a bound for the
deviation of the gauge marking of the terminal slice from the affine marking.
The defect `ε` was *assumed* there: nothing in the project estimated the
displacement of the gauge flow along an arbitrary normal path.

`MarkingDefectCost.lean` estimates it, from the linear growth of the field of
the gauge flow — the tangential rate `−ξ/v` of a bundle whose tangential
component vanishes at the base point and whose arclength derivative is bounded
by the geometry.  This file feeds that estimate into the bound: if the gauge
marking of the assembly is the flow of a globally Lipschitz field `R` obeying
`|R(t, x)| ≤ C t · |x|` with `C t ≤ κ · m t` for the cost density `m` of the
path, if it fixes the base point, and if it is quasi-periodic with the period
`Φ_t(1)` — the period at the final time being the perimeter of the marked
selected inverse of the terminal curve — then

```
  ‖(selInv κ̂ q).1 u − (selInv κ̂ p).1 u‖
      ≤ (gaugeJacobiConst … + 2·L_max·κ) · cost Γ
```

at every parameter: a bound proportional to the cost of the path alone, with no
defect assumed and no hypothesis on the parametrization of the terminal datum.

Main result: `sup_selInv_le_of_marking_flow_cost`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion
open scoped NNReal

namespace SelInvMarkingDefectCost

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The uniform comparison of the two marked selected inverses, with the
marking defect produced.**

Under the hypotheses of
`SelInvMarkingDefect.sup_selInv_le_of_marking_defect`, if the gauge marking of
the assembly is a flow of a globally Lipschitz field of linear growth
`|R(t, x)| ≤ C t·|x|` fixing the base point, quasi-periodic with period
`Φ_t(1) ≤ L_max`, normalized at the final time (`Φ_T(1)` is the perimeter of
`selInv κ̂ q`) and with growth coefficient at most `κ` times the cost density of
the path, then the two marked selected inverses differ by at most
`(gaugeJacobiConst … + 2 L_max κ)·cost Γ` at every parameter.

The linear growth of the field is what the geometry supplies: the tangential
component of the motion of the selected rears vanishes at the base point
(`GaugeBaseFlow.lean`) and its arclength derivative is bounded by the normal
velocity times `κ̂/√(1−κ̂²)` (`RearOwnTangential.lean`), so the tangential rate
`−ξ/v` obeys `|R(t, x)| ≤ C t·|x|` with `C` proportional to the cost density
(`MarkingDefectCost.abs_gaugeRate_le_mul_abs`). -/
theorem sup_selInv_le_of_marking_flow_cost {p q : Data} (Γ : NormalPath p q)
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
          ∀ (q' : Data) (R : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Klip' : ℝ≥0) (Lmax kappa : ℝ),
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ t, LipschitzWith Klip' (R t)) →
            (∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t) →
            (∀ u, Continuous fun t => R t (Phi t u)) →
            Continuous C → (∀ t x, |R t x| ≤ C t * |x|) → (∀ t, 0 ≤ C t) →
            (∀ t, Phi t 0 = 0) →
            (∀ t u, Phi t (u + 1) = Phi t u + Phi t 1) →
            (∀ t, Phi t 1 ≤ Lmax) →
            (∀ t, C t ≤ kappa * Γ.m t) →
            Phi Γ.T 1 = perim (SelectedInverseMap.selInv kh q) →
            Nonempty (NormalPath (SelectedInverseMap.selInv kh p) q') →
            ∀ u, ‖(SelectedInverseMap.selInv kh q).1 u - (SelectedInverseMap.selInv kh p).1 u‖
              ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ + 2 * Lmax * kappa * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hPhi⟩ :=
    SelInvMarkingDefect.sup_selInv_le_of_marking_defect Γ hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper
      hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv
  -- the perimeter of the marked selected inverse of the initial curve is positive
  obtain ⟨-, hdode0, hdmem0⟩ :=
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := 0) (hPpos 0) hdelta
      hKeq hsol hstrip hdnper
  have hdc0 : Continuous (δ 0) :=
    Differentiable.continuous fun s => (hdode0 s).differentiableAt
  have hL0pos : 0 < perim (SelectedInverseMap.selInv kh p) := by
    rw [hperimp]
    exact SelectedInverseUnique.rearArclength_pos (hPpos 0) hkh0 hkh1 hdc0 hdmem0
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, ?_⟩
  intro q' R C Klip' Lmax kappa hq' hlip hd hc' hCcont hgrow hCnn hPhibase hper hLmax
    hcost hPhiT hne
  refine hPhi q' (2 * Lmax * kappa * cost Γ) hq' (fun u => ?_) hne
  have hLmax0 : 0 ≤ Lmax := by
    refine le_trans ?_ (hLmax 0)
    rw [hPhi0 1, mul_one]
    exact hL0pos.le
  have h := MarkingDefectCost.abs_marking_defect_le_cost (K := Klip') (Lmax := Lmax)
    (L0 := perim (SelectedInverseMap.selInv kh p)) Γ hlip hd hc' hCcont
    (fun t x hx => le_trans (hgrow t x) (mul_le_mul_of_nonneg_left hx (hCnn t)))
    hPhi0 hL0pos (fun t _ => by rw [hPhibase t]; simpa using hLmax0) hper
    (fun t _ => hLmax t) hcost u
  rwa [hPhiT] at h

end SelInvMarkingDefectCost
