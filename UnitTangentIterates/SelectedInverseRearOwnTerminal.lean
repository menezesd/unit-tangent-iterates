import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnPath

/-!
# The terminal end of the path-distance bound

`SelectedInverseRearOwnPath.exists_marked_rearOwn_pathDist` states the
normalized path-distance bound for the selected rears of a normal path with the
*initial* marked curve identified: it is the value `selInv κ̂ p` of the
selected-inverse map of `SelectedInverseMap.lean` at the initial curve `p` of
the path.  Its terminal curve, on the other hand, is described only through the
gauge marking produced by the assembly, as
`x ↦ rearOwn … Γ.T (Phi Γ.T x)`.

This file identifies that terminal curve as well.  The identification of a
slice of the path with the marked selected inverse of that slice does not use
the time `0` in any way, so it is proved here once for an arbitrary time
(`ev_selInv_eq_rearOwn`): for a slice of the path which is a member of the tube,

```
  perim r = P t ,   ev r = frontOfPath X P t ,
  perim (selInv κ̂ r) = ∫₀^{P t} cos δ_t ,
  ev (selInv κ̂ r) x  = rearOwn F Θ δ sf t x .
```

Applying it at `t = Γ.T` gives the main result of the file,
`exists_marked_rearOwn_pathDist_terminal`: the terminal curve of the bound is
the marked selected inverse `selInv κ̂ q` of the terminal curve of the path,
**reparametrized by the gauge marking** `u ↦ Phi Γ.T u / perim (selInv κ̂ q)`.
The bound therefore reads

```
  pathDist (selInv κ̂ p) q' ≤ C · cost Γ ,
  q'.1 = (selInv κ̂ q).1 ∘ (Phi Γ.T · / perim (selInv κ̂ q)) .
```

What is still missing for the non-expansiveness of the selected inverse is that
the reparametrization is the identity — that is, that the gauge marking of the
terminal slice is the affine marking `u ↦ perim (selInv κ̂ q) * u` of
`selInv κ̂ q`; the gauge parameter is normalized but need not be affine in the
rear arclength.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseRearOwnTerminal

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn

variable {X V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-! ### The selected steering angle of one slice -/

/-- The steering angle of a slice, read off the normalized data: it is periodic
with the arclength period of that slice, it solves the steering equation for
the curvature of the slice, and it takes values in the closed strip. -/
theorem delta_slice_of_normalized {t : ℝ} (hP : 0 < P t)
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) :
    Function.Periodic (δ t) (P t) ∧
      (∀ s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s) ∧
      (∀ s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh)) := by
  have hne : P t ≠ 0 := hP.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [hdelta t (s + P t), hdelta t s]
    have h : (s + P t) / P t = s / P t + 1 := by field_simp
    rw [h, hdnper t]
  · intro s
    have hinner : HasDerivAt (fun s : ℝ => s / P t) (1 / P t) s := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P t)
    have h := (hsol t (s / P t)).comp s hinner
    have hfun : (dn t ∘ fun s : ℝ => s / P t) = δ t := funext fun s => (hdelta t s).symm
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [hKeq t s, hdelta t s]
    field_simp
  · intro s
    rw [hdelta t s]
    exact hstrip t (s / P t)

/-! ### A slice of the path and its marked selected inverse -/

/-- **The marked selected inverse of a slice of the path is the rear track of
that slice, written in its own arclength.**

If the curve of the marked datum `r` is the slice of `X` at the time `t`, and
`r` is a member of the tube of curvature pinched by `0 < kmin ≤ K ≤ κ̂ < 1`,
then the perimeter of `r` is the speed `P t` of the slice, the arclength
parametrization of `r` is the slice written in its own arclength, the perimeter
of `selInv κ̂ r` is the rear arclength period, and the arclength parametrization
of `selInv κ̂ r` is `rearOwn` at the time `t`.  Nothing here is special to the
time `0`. -/
theorem ev_selInv_eq_rearOwn {t c kmin dlt : ℝ} {r : Data}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkh1 : kh < 1)
    (hr : IsTubeMember c kmin dlt r)
    (hub : ∀ u, ((starRingEnd ℂ) (r.2.1 u) * r.2.2 u).im ≤ kh * ‖r.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev r) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim r) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev r) Θ' dl) (Ico 0 (perim r)))
    (hP : 0 < P t)
    (hV : ∀ u, HasDerivAt (X t) (V t u) u)
    (hA : ∀ u, HasDerivAt (V t) (A t u) u)
    (hAcont : Continuous (A t))
    (hspeed : ∀ u, ‖V t u‖ = P t)
    (hXr : X t = ⇑r.1)
    (hdper : Function.Periodic (δ t) (P t))
    (hdode : ∀ s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s)
    (hdmem : ∀ s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hsfinv : ∀ x, rearArclength (δ t) (sf t x) = x) :
    perim r = P t ∧ ev r = frontOfPath X P t ∧
      perim (SelectedInverseMap.selInv kh r) = rearArclength (δ t) (P t) ∧
      ∀ x, ev (SelectedInverseMap.selInv kh r) x
        = rearOwn (frontOfPath X P) (angleOfPath V A P) δ sf t x := by
  have hVcont : Continuous (V t) := continuous_iff_continuousAt.2 fun u => (hA u).continuousAt
  have hcurvcont : Continuous (curvOfPath V A P t) := continuous_curvOfPath hVcont hAcont
  -- the perimeter of `r` is the speed of the slice
  have hVr : ∀ u, V t u = r.2.1 u := by
    intro u
    have h1 : HasDerivAt (⇑r.1) (V t u) u := by rw [← hXr]; exact hV u
    exact h1.unique (hr.hasDerivAt_curve u)
  have hperim : perim r = P t := by rw [perim, ← hVr 0, hspeed 0]
  have hev : ev r = frontOfPath X P t := by
    funext s
    rw [ev, frontOfPath, hXr, hperim]
  -- the front data of the slice
  have hΘpath : ∀ s, HasDerivAt (frontOfPath X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro s
    rw [exp_angleOfPath hA hAcont hVcont hspeed hP s]
    exact hasDerivAt_frontOfPath_tangent hV hP s
  -- the marked selected inverse of `r`
  obtain ⟨-, Θ', K', dl, sf', hX', hΘ', hdper', hdmem', hode', hsfinv', hperim', hev'⟩ :=
    SelectedInverseMap.isMarkedSelectedInverse_selInv hc hkmin hkh1 hr hub hinjR
  -- the two tangent-angle lifts have the same exponential
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ' s : ℂ))
      = Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) := by
    intro s
    have h2 : HasDerivAt (ev r) (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
      rw [hev]; exact hΘpath s
    exact (hX' s).unique h2
  -- hence the same curvature
  have hK' : ∀ s, K' s = curvOfPath V A P t s := by
    intro s
    refine SelectedInverseTube.curvature_unique (Y := ev r)
      (th2 := angleOfPath V A P t) (k2 := curvOfPath V A P t) hX' ?_ hΘ' ?_ s
    · intro y; rw [hev]; exact hΘpath y
    · intro y; exact hasDerivAt_angleOfPath hcurvcont y
  -- the steering angles agree
  have hdleq : dl = δ t := by
    refine Shadowing.steering_unique (P := perim r) (K := curvOfPath V A P t)
      (perim_pos hc hr) ?_ ?_ hdper' ?_ ?_ ?_
    · intro s
      have h := hode' s
      rw [hK' s] at h
      exact h
    · exact hdode
    · rw [hperim]; exact hdper
    · intro s
      exact ⟨le_trans (by linarith [Real.pi_pos]) (hdmem' s).1,
        le_trans (hdmem' s).2 (Real.arcsin_le_pi_div_two kh)⟩
    · intro s
      exact ⟨le_trans (by linarith [Real.pi_pos]) (hdmem s).1,
        le_trans (hdmem s).2 (Real.arcsin_le_pi_div_two kh)⟩
  -- the changes of variable agree
  have hkh0 : (0 : ℝ) ≤ kh := Real.arcsin_nonneg.mp (le_trans (hdmem 0).1 (hdmem 0).2)
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hdc : Continuous (δ t) := Differentiable.continuous fun s => (hdode s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (δ t s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hmono : StrictMono (rearArclength (δ t)) :=
    strictMono_of_deriv_ge hcpos (fun s => hasDerivAt_rearArclength hdc s) hcos
  have hsfeq : sf' = sf t := by
    funext x
    refine hmono.injective ?_
    rw [← hdleq, hsfinv' x, hdleq, hsfinv x]
  refine ⟨hperim, hev, ?_, ?_⟩
  · rw [hperim', hdleq, hperim]
  · intro x
    rw [hev' x, hsfeq, hdleq, hev, rearOwn]
    exact SelectedInverseRearOwn.rearTrack_congr_angle hexp _

/-! ### The bound with both ends identified -/

/-- **The path-distance bound with the marked selected inverse at both ends.**

Under the hypotheses of
`SelectedInverseRearOwnPath.exists_marked_rearOwn_pathDist`, with the terminal
curve `q` of the path also a member of the tube, the terminal curve of the
bound is the marked selected inverse `selInv κ̂ q` of `q`, reparametrized by the
gauge marking `u ↦ Phi Γ.T u / perim (selInv κ̂ q)`: the path pseudodistance
from `selInv κ̂ p` to any marked curve whose curve is that reparametrization is
at most the gauge constant times the cost of `Γ`.

The two perimeters are identified as well: they are the rear arclength periods
of the initial and the terminal slice. -/
theorem exists_marked_rearOwn_pathDist_terminal {p q : Data} (Γ : NormalPath p q)
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
  -- the bound with the initial end identified
  obtain ⟨-, -, -, hperimp, -, -, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hPhi⟩ :=
    SelectedInverseRearOwnPath.exists_marked_rearOwn_pathDist Γ hc hkmin hp hub hinjR hP0
      hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol
      hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK
      hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hsfinv
  -- the terminal slice and its marked selected inverse
  obtain ⟨hdperT, hdodeT, hdmemT⟩ :=
    delta_slice_of_normalized (t := Γ.T) (hPpos Γ.T) hdelta hKeq hsol hstrip hdnper
  obtain ⟨-, -, hperimq, hevq⟩ :=
    ev_selInv_eq_rearOwn (X := Γ.X) (V := V) (A := A) (P := P) (δ := δ) (sf := sf)
      hcq hkminq hkh1 hq hubq hinjRq (hPpos Γ.T) (hV Γ.T) (hA Γ.T) (hAcont Γ.T)
      (hspeed Γ.T) (funext Γ.finish) hdperT hdodeT hdmemT (hsfinv Γ.T)
  refine ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, fun u => by rw [hPhi0 u, hperimp],
    hbase, ?_⟩
  intro q' hq'
  refine hPhi q' fun u => ?_
  rw [hq' u, ← hevq (Phi Γ.T u), ev]

end SelectedInverseRearOwnTerminal
