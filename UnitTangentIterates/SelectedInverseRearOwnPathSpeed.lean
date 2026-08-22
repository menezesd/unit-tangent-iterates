import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnPath
import UnitTangentIterates.RearOwnPathDistNormalizedSpeed

/-!
# The path-distance bound for the marked selected inverse, with the constant
fixed by the speed of the path

`SelectedInverseRearOwnPath.exists_marked_rearOwn_pathDist` bounds the path
pseudodistance of the selected rears of a normal path from the marked selected
inverse of its initial curve, but the sup bound `E_F` of the front normal
velocity occurring in its constant is produced by compactness, so that nothing
is known about it.

This file gives the same statement with `E_F` supplied by a bound `M` for the
**cost density of the path**, as `RearOwnPathDistNormalizedSpeed.lean` does one
step below.  The constant is then a function of the tube constants, of the
duration of the path and of `M` alone.

Main result: `exists_marked_rearOwn_pathDist_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnPathSpeed

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnPath

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path-distance bound with the marked selected inverse at the start,
with the front normal velocity bounded by the cost density of the path.**

Same statement as
`SelectedInverseRearOwnPath.exists_marked_rearOwn_pathDist`, with the sup bound
`E_F` of the front normal velocity replaced by any bound `M` for the cost
density of the path. -/
theorem exists_marked_rearOwn_pathDist_speed {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt M Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
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
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (SelectedInverseMap.selInv kh p))
        (kmin / Real.sqrt (1 - kmin ^ 2)) dR (SelectedInverseMap.selInv kh p) ∧
      perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      MainTheoremConditional.IsOval (ev (SelectedInverseMap.selInv kh p)) ∧
      range (UnitTangent.unitTangentMap (ev (SelectedInverseMap.selInv kh p)))
        = range (ev p) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u
            = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
          pathDist (SelectedInverseMap.selInv kh p) q' ≤ gaugeJacobiConst P0 P1 kh
              (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  -- the arclength period of the path at time `0` is the perimeter of `p`
  have hX0 : Γ.X 0 = ⇑p.1 := funext Γ.start
  have hVp : ∀ u, V 0 u = p.2.1 u := by
    intro u
    have h1 : HasDerivAt (⇑p.1) (V 0 u) u := by rw [← hX0]; exact hV 0 u
    exact h1.unique (hp.hasDerivAt_curve u)
  have hperimP : perim p = P 0 := by
    rw [perim, ← hVp 0, hspeed 0 0]
  have hevp : ev p = frontOfPath Γ.X P 0 := by
    funext s
    rw [ev, frontOfPath, hX0, hperimP]
  -- the front data of the marked curve
  have hΘpath : ∀ s, HasDerivAt (frontOfPath Γ.X P 0)
      (Complex.exp (Complex.I * (angleOfPath V A P 0 s : ℂ))) s := by
    intro s
    rw [exp_angleOfPath (hA 0) (hAcont 0) (hVcont 0) (hspeed 0) (hPpos 0) s]
    exact hasDerivAt_frontOfPath_tangent (hV 0) (hPpos 0) s
  -- the selected steering angle of the path at time `0`
  have hdper0 : Function.Periodic (δ 0) (P 0) := by
    intro s
    have hne : P 0 ≠ 0 := (hPpos 0).ne'
    rw [hdelta 0 (s + P 0), hdelta 0 s]
    have h : (s + P 0) / P 0 = s / P 0 + 1 := by field_simp
    rw [h, hdnper 0]
  have hdode0 : ∀ s, HasDerivAt (δ 0) (curvOfPath V A P 0 s - Real.sin (δ 0 s)) s := by
    intro s
    have hinner : HasDerivAt (fun s : ℝ => s / P 0) (1 / P 0) s := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P 0)
    have h := (hsol 0 (s / P 0)).comp s hinner
    have hfun : (dn 0 ∘ fun s : ℝ => s / P 0) = δ 0 := funext fun s => (hdelta 0 s).symm
    rw [hfun] at h
    refine h.congr_deriv ?_
    have hne : P 0 ≠ 0 := (hPpos 0).ne'
    rw [hKeq 0 s, hdelta 0 s]
    field_simp
  have hdmem0 : ∀ s, δ 0 s ∈ Icc (0 : ℝ) (Real.arcsin kh) := by
    intro s
    rw [hdelta 0 s]
    exact hstrip 0 (s / P 0)
  -- the marked selected inverse of `p`
  obtain ⟨p', Θ', K', dl, sf', dR, hX', hΘ', hKlow', hKhigh', hdper', hdmem', hode', hsfinv',
    hdRpos, hmem', hperim', hoval', hqub', hrange', hevp'x, hp'1⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn hc hkmin hkh1 hp hub hinjR
  -- the two tangent-angle lifts have the same exponential
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ' s : ℂ))
      = Complex.exp (Complex.I * (angleOfPath V A P 0 s : ℂ)) := by
    intro s
    have h1 : HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s := hX' s
    have h2 : HasDerivAt (ev p) (Complex.exp (Complex.I * (angleOfPath V A P 0 s : ℂ))) s := by
      rw [hevp]; exact hΘpath s
    exact h1.unique h2
  -- hence the same curvature
  have hK' : ∀ s, K' s = curvOfPath V A P 0 s := by
    intro s
    refine SelectedInverseTube.curvature_unique (Y := ev p)
      (th2 := angleOfPath V A P 0) (k2 := curvOfPath V A P 0) hX' ?_ hΘ' ?_ s
    · intro y; rw [hevp]; exact hΘpath y
    · intro y; exact hasDerivAt_angleOfPath (hcurvcont 0) y
  -- the steering angles agree
  have hdleq : dl = δ 0 := by
    refine Shadowing.steering_unique (P := perim p) (K := curvOfPath V A P 0)
      (perim_pos hc hp) ?_ ?_ hdper' ?_ ?_ ?_
    · intro s
      have h := hode' s
      rw [hK' s] at h
      exact h
    · exact hdode0
    · rw [hperimP]; exact hdper0
    · intro s
      exact ⟨le_trans (by linarith [Real.pi_pos]) (hdmem' s).1,
        le_trans (hdmem' s).2 (Real.arcsin_le_pi_div_two kh)⟩
    · intro s
      exact ⟨le_trans (by linarith [Real.pi_pos]) (hdmem0 s).1,
        le_trans (hdmem0 s).2 (Real.arcsin_le_pi_div_two kh)⟩
  -- the changes of variable agree
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hdc0 : Continuous (δ 0) :=
    Differentiable.continuous fun s => (hdode0 s).differentiableAt
  have hcos0 : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (δ 0 s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem0 s).1 (hdmem0 s).2
  have hmono0 : StrictMono (rearArclength (δ 0)) :=
    strictMono_of_deriv_ge hcpos (fun s => hasDerivAt_rearArclength hdc0 s) hcos0
  have hsfeq : sf' = sf 0 := by
    funext x
    refine hmono0.injective ?_
    rw [← hdleq, hsfinv' x, hdleq, hsfinv 0 x]
  -- the perimeter of the marked selected inverse is the rear period
  have hperimp' : perim p' = rearArclength (δ 0) (P 0) := by
    rw [hperim', hdleq, hperimP]
  -- the marked selected inverse is the initial curve of the bound
  have hstart : ∀ u, p'.1 u
      = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0
          (rearArclength (δ 0) (P 0) * u) := by
    intro u
    rw [hp'1 0 u, rearOwn, rearOwn, hperimp', hsfeq, hdleq, hevp]
    exact SelectedInverseRearOwn.rearTrack_congr_angle hexp _
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ :=
    RearOwnPathDistNormalizedSpeed.pathDist_le_of_path_normalized_speed Γ p' (M := M)
      hP0 hkh0 hkh1 hPl hPu hV hA
      hAcont hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper
      hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3
      hKdnC3 hFc4 hΘc4 hsfinv hm hstart
  -- `p'` is the value of the selected-inverse map at `p`
  have hp'eq : p' = SelectedInverseMap.selInv kh p :=
    SelectedInverseMap.selInv_eq hc hkmin hkh1 hp hub hinjR
      ⟨⟨perim p', kmin / Real.sqrt (1 - kmin ^ 2), dR, hmem'⟩,
        Θ', K', dl, sf', hX', hΘ', hdper', hdmem', hode', hsfinv', hperim', hevp'x⟩
  rw [hp'eq] at hmem' hperimp' hoval' hrange' hPhi
  exact ⟨dR, hdRpos, hmem', hperimp', hoval', hrange', Phi, hPhi0, hbase, hPhi⟩

end SelectedInverseRearOwnPathSpeed
