import UnitTangentIterates.SelectedInverseRearOwnFloorFree

/-!
# The marked selected inverse without a curvature floor

`SelectedInverseRearOwn.exists_marked_rearOwn` is what makes
`SelectedInverseMap.selInv` — the map `B` of the closing theorems — actually be
the rear map rather than its identity fallback.  It took `0 < kmin`.

Section 47 of the session log showed the main theorem is not instantiable with a
positive curvature floor, so this theorem had to be freed of it.  Its four uses
of `kmin` turn out to be:

* `0 ≤ kap`, which follows from `0 ≤ K 0 ≤ kap` directly;
* the lower bound fed to `exists_periodic_steering`, which is `0 ≤ K`;
* `isOval_rearOwn`, replaced by `isOval_rearOwn_floor_free`;
* `selected_rear_curvature_pinched`, which only ever consumed `0 ≤ kmin`.

None was analytic.  The rear tube produced now carries floor `0`, which is
exactly what the floor-free closing chain of `PathSchemePullbackHarnack`
consumes.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MarkedSpace RearTrack ArclengthInverse RearOwnArclength

namespace SelectedInverseRearOwn

variable {Θ K dl sf : ℝ → ℝ} {F : ℝ → ℂ} {P kap : ℝ}

theorem exists_marked_rearOwn_floor_free {c delta : ℝ} (hc : 0 < c)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c 0 delta p)
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
      (∀ s, HasDerivAt Θ (K s) s) ∧ (∀ s, 0 ≤ K s) ∧ (∀ s, K s ≤ kap) ∧
      Function.Periodic dl (perim p) ∧ (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) ∧
      (∀ x, rearArclength dl (sf x) = x) ∧
      0 < dR ∧ IsTubeMember (perim q) 0 dR q ∧
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
  have hkap0 : 0 ≤ kap := le_trans (hKlow 0) (hKhigh 0)
  have hKne : ∃ s, K s ≠ 0 := by
    obtain ⟨s, hs⟩ := UnconditionalAssembly.arcCurv_nonzero hc hp
    exact ⟨s, by rw [RearTrackEmbedded.curvature_eq_arcCurv hc hp hX hΘ s]; exact hs⟩
  obtain ⟨dl, hdper, hdmem, hdcos, hode⟩ :=
    SteeringExistence.exists_periodic_steering hPpos hKc hKper hkap0 hkap1.le
      hKlow hKhigh
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
    isOval_rearOwn_floor_free hPpos hkap1 hX hΘ hFper hKlow hKne hKhigh hdc hdper hdmem
      hode hsfinv (hinjR Θ K dl hX hΘ hdper hdmem hode)
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
  have hpinch := LowCurvatureAssembly.selected_rear_curvature_pinched hPpos (le_refl (0:ℝ))
    hkap1 hdper hode hdmem hKlow
  have hlow0 : ∀ x, (0:ℝ) ≤ Real.tan (dl (sf x)) := by
    intro x
    have h := (hpinch (sf x)).1
    simpa using h
  obtain ⟨q, L, dR, hLpos, hdRpos, hmem, hperimq, hevq, hLmin, hqub⟩ :=
    SelectedInverseTube.exists_tube_member_of_oval_data hoval hYderiv hthderiv hkYc
      hlow0 (fun x => (hpinch (sf x)).2)
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
