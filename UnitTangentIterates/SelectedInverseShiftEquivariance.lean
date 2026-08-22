import Mathlib
import UnitTangentIterates.MarkedShift
import UnitTangentIterates.SelectedInverseMap

/-!
# The selected inverse is equivariant for shifts of the marking

`MarkedShift.lean` takes the path pseudodistance modulo the marking, because
the gauge flow moves the base point of a curve along it.  For that quotient to
be meaningful for the shadowing scheme, the selected inverse must respect it:
the marked selected inverse of a shifted curve must be a shift of the marked
selected inverse.

That is proved here.  If `p` is a member of the tube and `b` a shift, the front
data of `p` shifted by `b·perim p` are front data of `shiftData b p`, the
selected steering angle shifts with them, the rear arclength shifts by the
constant `∫₀^{b·perim p} cos δ`, and the rear track written in its own
arclength is therefore the one of `p`, marked at that point.  By uniqueness of
the marked selected inverse,

```
  selInv κ̂ (shiftData b p) = shiftData c (selInv κ̂ p) ,
  c = (∫₀^{b·perim p} cos δ) / perim (selInv κ̂ p) .
```

As everywhere in this project, the global topological fact that the rear track
of the shifted curve is embedded is carried as an explicit hypothesis.

Main result: `selInv_shiftData`.
-/

noncomputable section

open Set Function MarkedSpace RearTrack ArclengthInverse MarkedShift

namespace SelectedInverseShiftEquivariance

/-! ### Elementary properties of the shift -/

theorem perim_shiftData {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p)
    (b : ℝ) : perim (shiftData b p) = perim p := by
  simp only [perim, shiftData_vel, zero_add]
  exact hp.speed_const b 0

theorem ev_shiftData {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p)
    (hL : perim p ≠ 0) (b s : ℝ) :
    ev (shiftData b p) s = ev p (s + b * perim p) := by
  simp only [ev, perim_shiftData hp b, shiftData_curve]
  congr 1
  field_simp

/-- The rear arclength of a shifted steering angle. -/
theorem rearArclength_shift {dl : ℝ → ℝ} (hdc : Continuous dl) (t y : ℝ) :
    rearArclength (fun s => dl (s + t)) y
      = rearArclength dl (y + t) - rearArclength dl t := by
  have hcont : Continuous fun s => Real.cos (dl s) := Real.continuous_cos.comp hdc
  simp only [rearArclength]
  rw [intervalIntegral.integral_comp_add_right (fun s => Real.cos (dl s)) t,
    intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  ring_nf

/-- The rear arclength grows by the rear period over each period of the
steering angle. -/
theorem rearArclength_add_period {dl : ℝ → ℝ} {L : ℝ} (hdc : Continuous dl)
    (hper : Function.Periodic dl L) (x : ℝ) :
    rearArclength dl (x + L) = rearArclength dl x + rearArclength dl L := by
  have hcont : Continuous fun s => Real.cos (dl s) := Real.continuous_cos.comp hdc
  have hcper : Function.Periodic (fun s => Real.cos (dl s)) L := fun s => by
    simp [hper s]
  have hsplit : (∫ u in (0:ℝ)..(x + L), Real.cos (dl u))
      = (∫ u in (0:ℝ)..x, Real.cos (dl u)) + ∫ u in x..(x + L), Real.cos (dl u) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hshift : (∫ u in x..(x + L), Real.cos (dl u))
      = ∫ u in (0:ℝ)..(0 + L), Real.cos (dl u) := hcper.intervalIntegral_add_eq x 0
  simp only [rearArclength]
  rw [hsplit, hshift, zero_add]

/-! ### The equivariance -/

/-- **The selected inverse is equivariant for shifts of the marking.**  The
marked selected inverse of a shifted member of the tube is the marked selected
inverse of that member, marked at another point. -/
theorem selInv_shiftData {c kmin dlt kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p)))
    (b : ℝ)
    (hinjRb : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (shiftData b p)) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim (shiftData b p)) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev (shiftData b p)) Θ dl) (Ico 0 (perim (shiftData b p)))) :
    ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b p)
      = shiftData cc (SelectedInverseMap.selInv kap p) := by
  set L : ℝ := perim p with hLdef
  have hLpos : 0 < L := perim_pos hc hp
  set q : Data := SelectedInverseMap.selInv kap p with hqdef
  obtain ⟨⟨c₁, k₁, d₁, hq₁⟩, Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, hperim, hev⟩ :=
    SelectedInverseMap.isMarkedSelectedInverse_selInv hc hkmin hkap1 hp hub hinjR
  have hkap0 : (0 : ℝ) ≤ kap := Real.arcsin_nonneg.mp (le_trans (hdmem 0).1 (hdmem 0).2)
  have hdc : Continuous dl := Differentiable.continuous fun s => (hode s).differentiableAt
  have hQpos : 0 < perim q := by
    rw [hperim]
    exact SelectedInverseUnique.rearArclength_pos hLpos hkap0 hkap1 hdc hdmem
  -- the shifted data
  set t : ℝ := b * L with htdef
  set a : ℝ := rearArclength dl t with hadef
  refine ⟨a / perim q, ?_⟩
  have hpb : IsTubeMember c kmin dlt (shiftData b p) := isTubeMember_shiftData hp b
  have hperimb : perim (shiftData b p) = L := perim_shiftData hp b
  have hevb : ∀ s, ev (shiftData b p) s = ev p (s + t) := fun s => ev_shiftData hp hLpos.ne' b s
  have hubb : ∀ u, ((starRingEnd ℂ) ((shiftData b p).2.1 u) * (shiftData b p).2.2 u).im
      ≤ kap * ‖(shiftData b p).2.1 u‖ ^ 3 := by
    intro u
    simpa using hub (u + b)
  -- the data of the marked selected inverse of the shifted curve
  have hinner : ∀ s : ℝ, HasDerivAt (fun y : ℝ => y + t) 1 s := fun s => by
    simpa using (hasDerivAt_id s).add_const t
  have hXb : ∀ s, HasDerivAt (ev (shiftData b p))
      (Complex.exp (Complex.I * ((Θ (s + t) : ℝ) : ℂ))) s := by
    intro s
    have h : HasDerivAt (fun y => ev p (y + t))
        (Complex.exp (Complex.I * ((Θ (s + t) : ℝ) : ℂ))) s := by
      simpa using (hX (s + t)).scomp s (hinner s)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => hevb y)
  have hΘb : ∀ s, HasDerivAt (fun y => Θ (y + t)) (K (s + t)) s := fun s => by
    simpa using (hΘ (s + t)).scomp s (hinner s)
  have hdperb : Function.Periodic (fun y => dl (y + t)) (perim (shiftData b p)) := by
    rw [hperimb]
    intro s
    have h : s + L + t = s + t + L := by ring
    simp only [h]
    exact hdper (s + t)
  have hdmemb : ∀ s, dl (s + t) ∈ Icc 0 (Real.arcsin kap) := fun s => hdmem (s + t)
  have hodeb : ∀ s, HasDerivAt (fun y => dl (y + t))
      (K (s + t) - Real.sin (dl (s + t))) s := fun s => by
    simpa using (hode (s + t)).scomp s (hinner s)
  have hrs : ∀ y, rearArclength (fun s => dl (s + t)) y
      = rearArclength dl (y + t) - a := fun y => rearArclength_shift hdc t y
  have hsfinvb : ∀ x, rearArclength (fun s => dl (s + t)) (sf (x + a) - t) = x := by
    intro x
    rw [hrs]
    have h : sf (x + a) - t + t = sf (x + a) := by ring
    rw [h, hsfinv (x + a)]
    ring
  have hperimqb : perim (shiftData (a / perim q) q)
      = rearArclength (fun s => dl (s + t)) (perim (shiftData b p)) := by
    rw [perim_shiftData hq₁, hperimb, hrs L, hperim, ← hLdef]
    have h : rearArclength dl (L + t) = rearArclength dl t + rearArclength dl L := by
      rw [add_comm L t, rearArclength_add_period hdc hdper t]
    rw [h, ← hadef]
    ring
  have hevqb : ∀ x, ev (shiftData (a / perim q) q) x
      = rearTrack (ev (shiftData b p)) (fun y => Θ (y + t)) (fun y => dl (y + t))
          (sf (x + a) - t) := by
    intro x
    have h1 : ev (shiftData (a / perim q) q) x = ev q (x + a) := by
      rw [ev_shiftData hq₁ hQpos.ne' (a / perim q) x]
      congr 1
      field_simp
      rw [← hqdef]
      ring
    have h2 : sf (x + a) - t + t = sf (x + a) := by ring
    rw [h1, hev (x + a)]
    simp only [rearTrack, rearAngle, hevb (sf (x + a) - t), h2]
  refine (SelectedInverseMap.selInv_eq hc hkmin hkap1 hpb hubb hinjRb ?_).symm
  exact ⟨⟨c₁, k₁, d₁, isTubeMember_shiftData hq₁ (a / perim q)⟩,
    (fun y => Θ (y + t)), (fun y => K (y + t)), (fun y => dl (y + t)),
    (fun x => sf (x + a) - t), hXb, hΘb, hdperb, hdmemb, hodeb, hsfinvb, hperimqb, hevqb⟩

end SelectedInverseShiftEquivariance
