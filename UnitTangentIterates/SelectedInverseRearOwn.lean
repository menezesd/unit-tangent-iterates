import Mathlib
import UnitTangentIterates.SelectedInverseTube
import UnitTangentIterates.RearOwnArclength

/-!
# The marked selected inverse, written in its own arclength

`SelectedInverseTube.exists_tube_member_rear` produces the **marked selected
inverse** of a member `p` of the tube: a marked curve `q` whose unit-tangent
transform retraces `p`.  The assembly of the path metric, on the other hand,
speaks of the selected rear in the concrete form

```
  rearOwn F Θ δ sf t x = R(t, sf(t, x)) ,   R = F - e^{i(Θ-δ)} ,
```

the rear track of the front written in its own arclength (`RearOwnArclength`),
and its endpoint hypotheses (`hstart` of
`RearOwnPathDistNormalized.pathDist_le_of_front_normalized`) ask the marked
data at the ends of the path to be exactly that curve, marked at the point
`x = 0` and rescaled by the rear period.

This file identifies the two.  Starting from a tube member `p` of curvature
pinched by `0 < kmin ≤ K ≤ κ̂ < 1`, the front data of `p` are read off, the
selected steering angle `δ` is produced, the rear arclength is inverted, and
the rear track written in its own arclength is shown to be an oval; feeding it
to `SelectedInverseTube.exists_tube_member_of_oval_data` gives a member `q` of
the tube with

```
  perim q = ∫₀^{perim p} cos δ ,      ev q = R ∘ sf ,
  q.1 u   = rearOwn (fun _ => ev p) (fun _ => Θ) (fun _ => δ) (fun _ => sf) t
              (perim q * u) ,
```

that is: **the marked selected inverse of `p` is the rear track of `p` written
in its own arclength, marked at `x = 0`.**  Its unit-tangent transform retraces
`p`, its curvature is pinched by `kmin/√(1-kmin²)` and `κ̂/√(1-κ̂²)`, and its
chord-arc constant is produced rather than assumed.

As everywhere in this project, the global topological fact that the rear track
is embedded is carried as an explicit hypothesis.

Main results:

* `exists_marked_rearOwn` — the identification above;
* `rearOwn_marked_of_data` — the same statement with the front data, the
  steering angle and the change of variable given, rather than produced.
-/

noncomputable section

open Set Function Complex MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseRearOwn

variable {Θ K dl sf : ℝ → ℝ} {F : ℝ → ℂ} {P kap kmin : ℝ}

/-! ### The rear track in its own arclength is an oval -/

section Oval

/-- The rear period `Q = ∫₀^P cos δ` is positive. -/
theorem rearPeriod_pos (hP : 0 < P) {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) : 0 < rearArclength dl P := by
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_of_deriv_ge hc (fun s => hasDerivAt_rearArclength hdc s) hcos
  have h0 : rearArclength dl 0 = 0 := by simp [rearArclength]
  have := hmono hP
  rwa [h0] at this

/-- The change of variable `sf` is the inverse of the rear arclength: it is
strictly monotone and fixes the marked point. -/
theorem sf_strictMono {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x) :
    StrictMono sf := by
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_of_deriv_ge hc (fun s => hasDerivAt_rearArclength hdc s) hcos
  intro x y hxy
  by_contra hle
  push_neg at hle
  have := hmono.le_iff_le.2 hle
  rw [hsfinv, hsfinv] at this
  linarith

theorem sf_zero {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x) :
    sf 0 = 0 := by
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_of_deriv_ge hc (fun s => hasDerivAt_rearArclength hdc s) hcos
  refine hmono.injective ?_
  rw [hsfinv]
  simp [rearArclength]

theorem sf_rearPeriod {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x) :
    sf (rearArclength dl P) = P := by
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_of_deriv_ge hc (fun s => hasDerivAt_rearArclength hdc s) hcos
  exact hmono.injective (hsfinv _)

/-- The unit tangent of the front is `P`-periodic as soon as the front is. -/
theorem expFront_periodic (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hFper : Function.Periodic F P) (s : ℝ) :
    Complex.exp (Complex.I * (Θ (s + P) : ℂ)) = Complex.exp (Complex.I * (Θ s : ℂ)) :=
  SelectedInverseOval.expTangent_periodic hF hFper s

/-- The rear track is `P`-periodic. -/
theorem rearTrack_periodic (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hFper : Function.Periodic F P) (hdper : Function.Periodic dl P) :
    Function.Periodic (rearTrack F Θ dl) P := by
  intro s
  have hsplit : ∀ t : ℝ, Complex.exp (Complex.I * (rearAngle Θ dl t : ℂ))
      = Complex.exp (Complex.I * (Θ t : ℂ)) * Complex.exp (-(Complex.I * (dl t : ℂ))) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    simp [rearAngle]
    ring
  simp only [rearTrack, hsplit, hFper s, hdper s, expFront_periodic hF hFper s]

/-- The change of variable translates the rear period into the front period. -/
theorem sf_add_rearPeriod {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hdper : Function.Periodic dl P)
    (hsfinv : ∀ x, rearArclength dl (sf x) = x) (x : ℝ) :
    sf (x + rearArclength dl P) = sf x + P := by
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_of_deriv_ge hc (fun s => hasDerivAt_rearArclength hdc s) hcos
  refine hmono.injective ?_
  rw [hsfinv, rearArclength_add_period hdc hdper (sf x), hsfinv x]

/-- **The rear track in its own arclength closes up** with the rear period. -/
theorem periodic_rearOwn {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hdper : Function.Periodic dl P)
    (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hFper : Function.Periodic F P) :
    Function.Periodic (fun x => rearTrack F Θ dl (sf x)) (rearArclength dl P) := by
  intro x
  simp only [sf_add_rearPeriod hc hdc hcos hdper hsfinv x,
    rearTrack_periodic hF hFper hdper (sf x)]

/-- **The rear track in its own arclength is embedded** on a period, as soon as
the rear track is. -/
theorem injOn_rearOwn {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hinj : InjOn (rearTrack F Θ dl) (Ico 0 P)) :
    InjOn (fun x => rearTrack F Θ dl (sf x)) (Ico 0 (rearArclength dl P)) := by
  have hsfmono : StrictMono sf := sf_strictMono hc hdc hcos hsfinv
  have hsf0 : sf 0 = 0 := sf_zero hc hdc hcos hsfinv
  have hsfQ : sf (rearArclength dl P) = P := sf_rearPeriod hc hdc hcos hsfinv
  intro x hx y hy hxy
  have hxmem : sf x ∈ Ico (0 : ℝ) P :=
    ⟨by rw [← hsf0]; exact hsfmono.monotone hx.1, by rw [← hsfQ]; exact hsfmono hx.2⟩
  have hymem : sf y ∈ Ico (0 : ℝ) P :=
    ⟨by rw [← hsf0]; exact hsfmono.monotone hy.1, by rw [← hsfQ]; exact hsfmono hy.2⟩
  exact hsfmono.injective (hinj hxmem hymem hxy)

/-- **The rear track in its own arclength has unit speed**, of tangent angle
`Ψ ∘ sf`. -/
theorem hasDerivAt_rearOwnCurve {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) (x : ℝ) :
    HasDerivAt (fun x => rearTrack F Θ dl (sf x))
      (Complex.exp (Complex.I * (rearAngle Θ dl (sf x) : ℂ))) x := by
  have hcospos : ∀ s, 0 < Real.cos (dl s) := fun s => lt_of_lt_of_le hc (hcos s)
  have hsf : ∀ x, HasDerivAt sf (1 / Real.cos (dl (sf x))) x := fun x =>
    hasDerivAt_of_rightInverse hc (fun s => hasDerivAt_rearArclength hdc s) hcos hsfinv x
  have h := (hasDerivAt_rearTrack (hF (sf x)) (hΘ (sf x)) (hode (sf x))).scomp x (hsf x)
  refine h.congr_deriv ?_
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, one_div,
    inv_mul_cancel₀ (hcospos (sf x)).ne']
  simp

/-- **The curvature of the rear track in its own arclength** is `tan δ`. -/
theorem hasDerivAt_rearOwnAngleSf {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) (x : ℝ) :
    HasDerivAt (fun z => rearAngle Θ dl (sf z)) (Real.tan (dl (sf x))) x := by
  have hcospos : ∀ s, 0 < Real.cos (dl s) := fun s => lt_of_lt_of_le hc (hcos s)
  have hsf : ∀ x, HasDerivAt sf (1 / Real.cos (dl (sf x))) x := fun x =>
    hasDerivAt_of_rightInverse hc (fun s => hasDerivAt_rearArclength hdc s) hcos hsfinv x
  have h := (hasDerivAt_rearAngle (hΘ (sf x)) (hode (sf x))).comp x (hsf x)
  refine h.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  have := (hcospos (sf x)).ne'
  field_simp

end Oval

/-- **The rear track in its own arclength is an oval.**  For an admissible
front `F` of tangent angle `Θ`, curvature `K` pinched by `0 < kmin ≤ K ≤ κ̂ < 1`
and period `P`, with a selected steering angle `δ` on the closed strip and a
right inverse `sf` of the rear arclength, the curve `Y = R ∘ sf` — the rear
track written in its own arclength — is an oval of period
`Q = ∫₀^P cos δ`, of unit speed with tangent angle `Ψ ∘ sf` and curvature
`tan δ ∘ sf`. -/
theorem isOval_rearOwn (hP : 0 < P) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hFper : Function.Periodic F P)
    (hKlow : ∀ s, kmin ≤ K s) (hKhigh : ∀ s, K s ≤ kap)
    (hdc : Continuous dl) (hdper : Function.Periodic dl P)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap))
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hinj : InjOn (rearTrack F Θ dl) (Ico 0 P)) :
    MainTheoremConditional.IsOval (fun x => rearTrack F Θ dl (sf x)) := by
  have hkap0 : 0 ≤ kap := le_trans hkmin.le (le_trans (hKlow 0) (hKhigh 0))
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hpinch := LowCurvatureAssembly.selected_rear_curvature_pinched hP hkmin.le hkap1
    hdper hode hdmem hKlow
  have hkmin1 : kmin < 1 := lt_of_le_of_lt (le_trans (hKlow 0) (hKhigh 0)) hkap1
  refine ⟨rearArclength dl P, rearPeriod_pos hP hcpos hdc hcos,
    periodic_rearOwn hcpos hdc hcos hdper hsfinv hF hFper,
    injOn_rearOwn hcpos hdc hcos hsfinv hinj,
    fun x => rearAngle Θ dl (sf x),
    fun x => hasDerivAt_rearOwnCurve hcpos hdc hcos hsfinv hF hΘ hode x,
    fun x => Real.tan (dl (sf x)),
    fun x => hasDerivAt_rearOwnAngleSf hcpos hdc hcos hsfinv hΘ hode x, fun x => ?_⟩
  refine lt_of_lt_of_le ?_ (hpinch (sf x)).1
  exact div_pos hkmin (Real.sqrt_pos.mpr (by nlinarith))

/-- **The rear track does not depend on the choice of the tangent-angle lift.**
Two lifts with the same exponential give the same rear track. -/
theorem rearTrack_congr_angle {F : ℝ → ℂ} {Θ₁ Θ₂ dl : ℝ → ℝ}
    (h : ∀ s, Complex.exp (Complex.I * (Θ₁ s : ℂ)) = Complex.exp (Complex.I * (Θ₂ s : ℂ)))
    (s : ℝ) : rearTrack F Θ₁ dl s = rearTrack F Θ₂ dl s := by
  have hsplit : ∀ Θ : ℝ → ℝ, Complex.exp (Complex.I * (rearAngle Θ dl s : ℂ))
      = Complex.exp (Complex.I * (Θ s : ℂ)) * Complex.exp (-(Complex.I * (dl s : ℂ))) := by
    intro Θ
    rw [← Complex.exp_add]
    congr 1
    simp [rearAngle]
    ring
  simp only [rearTrack, hsplit, h s]

/-! ### The marked selected inverse of a tube member -/

/-- **The marked selected inverse is the rear track in its own arclength.**

Let `p` be a member of the tube whose curvature, in arclength, is pinched by
`0 < kmin ≤ K ≤ κ̂ < 1`.  Then there are front data `Θ, K` for `p`, a selected
steering angle `δ` on the closed strip, a right inverse `sf` of the rear
arclength, and a member `q` of the tube such that

```
  perim q = ∫₀^{perim p} cos δ ,
  ev q  x = R(sf x) ,          R = ev p - e^{i(Θ-δ)} ,
  q.1   u = R(sf (perim q · u)) ,
```

that is, the marked curve `q` is exactly the rear track of `p` written in its
own arclength and marked at `x = 0` — the object the endpoint hypotheses of the
path-metric assembly refer to.  Moreover `q` is an oval whose unit-tangent
transform retraces `p`, its curvature is pinched by `kmin/√(1-kmin²)` and
`κ̂/√(1-κ̂²)`, and its chord-arc constant `dR` is produced rather than assumed.

As everywhere in this project, the embeddedness of the rear track is carried as
an explicit hypothesis. -/
theorem exists_marked_rearOwn {c delta : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c kmin delta p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    ∃ (q : Data) (Θ K dl sf : ℝ → ℝ) (dR : ℝ),
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ (K s) s) ∧ (∀ s, kmin ≤ K s) ∧ (∀ s, K s ≤ kap) ∧
      Function.Periodic dl (perim p) ∧ (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) ∧
      (∀ x, rearArclength dl (sf x) = x) ∧
      0 < dR ∧ IsTubeMember (perim q) (kmin / Real.sqrt (1 - kmin ^ 2)) dR q ∧
      perim q = rearArclength dl (perim p) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      (∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) * ‖q.2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev p) ∧
      (∀ x, ev q x = rearTrack (ev p) Θ dl (sf x)) ∧
      (∀ t u, q.1 u
        = RearOwnArclength.rearOwn (fun _ => ev p) (fun _ => Θ) (fun _ => dl)
            (fun _ => sf) t (perim q * u)) := by
  have hPpos : 0 < perim p := perim_pos hc hp
  obtain ⟨Θ, K, hKc, hKper, hX, hΘ, hKlow, hKhigh⟩ :=
    SelectedInverseTube.exists_front_data hc hp hub
  have hkap0 : 0 ≤ kap := le_trans hkmin.le (le_trans (hKlow 0) (hKhigh 0))
  obtain ⟨dl, hdper, hdmem, hdcos, hode⟩ :=
    SteeringExistence.exists_periodic_steering hPpos hKc hKper hkap0 hkap1.le
      (fun s => le_trans hkmin.le (hKlow s)) hKhigh
  have hdc : Continuous dl := Differentiable.continuous fun s => (hode s).differentiableAt
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  obtain ⟨sf, hsfinv⟩ :=
    exists_rightInverse hcpos (fun s => hasDerivAt_rearArclength hdc s) hdcos
  have hsfc : Continuous sf :=
    continuous_of_rightInverse hcpos (fun s => hasDerivAt_rearArclength hdc s) hdcos hsfinv
  have hcospos : ∀ s, 0 < Real.cos (dl s) := fun s => lt_of_lt_of_le hcpos (hdcos s)
  have hQpos : 0 < rearArclength dl (perim p) := rearPeriod_pos hPpos hcpos hdc hdcos
  have hFper : Function.Periodic (ev p) (perim p) := periodic_ev hc hp
  have hoval : MainTheoremConditional.IsOval (fun x => rearTrack (ev p) Θ dl (sf x)) :=
    isOval_rearOwn hPpos hkmin hkap1 hX hΘ hFper hKlow hKhigh hdc hdper hdmem hode hsfinv
      (hinjR Θ K dl hX hΘ hdper hdmem hode)
  have hYderiv : ∀ x, HasDerivAt (fun x => rearTrack (ev p) Θ dl (sf x))
      (Complex.exp (Complex.I * (rearAngle Θ dl (sf x) : ℂ))) x := fun x =>
    hasDerivAt_rearOwnCurve hcpos hdc hdcos hsfinv hX hΘ hode x
  have hthderiv : ∀ x, HasDerivAt (fun z => rearAngle Θ dl (sf z))
      (Real.tan (dl (sf x))) x := fun x =>
    hasDerivAt_rearOwnAngleSf hcpos hdc hdcos hsfinv hΘ hode x
  have hkYc : Continuous fun x => Real.tan (dl (sf x)) := by
    have hcomp : Continuous fun x => dl (sf x) := hdc.comp hsfc
    have heq : (fun x => Real.tan (dl (sf x)))
        = fun x => Real.sin (dl (sf x)) / Real.cos (dl (sf x)) :=
      funext fun x => Real.tan_eq_sin_div_cos _
    rw [heq]
    exact (Real.continuous_sin.comp hcomp).div (Real.continuous_cos.comp hcomp)
      (fun x => (hcospos (sf x)).ne')
  have hpinch := LowCurvatureAssembly.selected_rear_curvature_pinched hPpos hkmin.le hkap1
    hdper hode hdmem hKlow
  obtain ⟨q, L, dR, hLpos, hdRpos, hmem, hperimq, hevq, hLmin, hqub⟩ :=
    SelectedInverseTube.exists_tube_member_of_oval_data hoval hYderiv hthderiv hkYc
      (fun x => (hpinch (sf x)).1) (fun x => (hpinch (sf x)).2)
  -- the period of the marked selected inverse is the rear period
  have hLQ : L = rearArclength dl (perim p) := by
    have hYper : Function.Periodic (fun x => rearTrack (ev p) Θ dl (sf x))
        (rearArclength dl (perim p)) :=
      periodic_rearOwn hcpos hdc hdcos hdper hsfinv hX hFper
    have hle : L ≤ rearArclength dl (perim p) := hLmin _ hQpos hYper
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have hYperL : Function.Periodic (fun x => rearTrack (ev p) Θ dl (sf x)) L := by
      have h := periodic_ev hLpos hmem
      rw [hperimq, hevq] at h
      exact h
    have hinjY : InjOn (fun x => rearTrack (ev p) Θ dl (sf x))
        (Ico 0 (rearArclength dl (perim p))) :=
      injOn_rearOwn hcpos hdc hdcos hsfinv (hinjR Θ K dl hX hΘ hdper hdmem hode)
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (rearArclength dl (perim p)) := ⟨le_rfl, hQpos⟩
    have hL0 : L ∈ Ico (0 : ℝ) (rearArclength dl (perim p)) := ⟨hLpos.le, hlt⟩
    have hval : (fun x => rearTrack (ev p) Θ dl (sf x)) L
        = (fun x => rearTrack (ev p) Θ dl (sf x)) 0 := by
      simpa using hYperL 0
    exact absurd (hinjY hL0 h0 hval) hLpos.ne'
  have hperimQ : perim q = rearArclength dl (perim p) := by rw [hperimq, hLQ]
  have hevqx : ∀ x, ev q x = rearTrack (ev p) Θ dl (sf x) := fun x => by rw [hevq]
  refine ⟨q, Θ, K, dl, sf, dR, hX, hΘ, hKlow, hKhigh, hdper, hdmem, hode, hsfinv, hdRpos,
    by rw [hperimq]; exact hmem, hperimQ, by rw [hevq]; exact hoval, hqub, ?_, hevqx, ?_⟩
  · -- the unit-tangent transform of the marked selected inverse retraces `p`
    have hsfsurj : Function.Surjective sf := by
      intro s
      refine ⟨rearArclength dl s, ?_⟩
      have hmono : StrictMono (rearArclength dl) :=
        strictMono_of_deriv_ge hcpos (fun t => hasDerivAt_rearArclength hdc t) hdcos
      exact leftInverse_of_rightInverse hmono.injective hsfinv s
    have hpt : ∀ x, UnitTangent.unitTangentMap (ev q) x = ev p (sf x) := by
      intro x
      have hderiv : ∀ y, HasDerivAt (ev q)
          (Complex.exp (Complex.I * (rearAngle Θ dl (sf y) : ℂ))) y := by
        intro y
        rw [hevq]
        exact hYderiv y
      rw [UnitTangent.unitTangentMap, (hderiv x).deriv, hevqx x,
        RearTrack.unitTangentMap_rearTrack]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨sf x, (hpt x).symm⟩
    · rintro _ ⟨s, rfl⟩
      obtain ⟨x, rfl⟩ := hsfsurj s
      exact ⟨x, hpt x⟩
  · -- the marked curve is the rear track in its own arclength, marked at `x = 0`
    intro t u
    have hQne : perim q ≠ 0 := by rw [hperimQ]; exact hQpos.ne'
    have h : ev q (perim q * u) = q.1 u := by
      simp only [ev]
      rw [mul_comm, mul_div_assoc, div_self hQne, mul_one]
    rw [← h, hevqx, RearOwnArclength.rearOwn]

end SelectedInverseRearOwn
