import Mathlib
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Embeddedness of the rear tracks is invariant under a shift of the marking

`SelectedInverseShiftEquivariance.selInv_shiftData` — the equivariance of the
selected inverse for shifts of the marking — and the non-expansiveness statement
built on it (`SelectedInverseQuotient.pathDistShift_selInv_le_pathDistShift_of_tube`)
carry the embeddedness of the rear tracks as a hypothesis **for every shift of
the marking** as well as for the curve itself.

That is redundant.  Shifting the marking translates the arclength parameter, so
the rear track of the shifted data is the rear track of the original data read
from another point; and the rear track of a closed curve is periodic with the
perimeter, its three ingredients being so: the arclength parametrization is,
the steering angle is by hypothesis, and the unit tangent is, being the
derivative of a periodic function.  A curve injective on one fundamental
interval is therefore injective on every one.

Main results:

* `injOn_Ico_of_periodic` — a periodic map injective on `[0,L)` is injective on
  every interval `[a, a+L)`;
* `periodic_rearTrack` — the rear track of a member of the tube is periodic
  with the perimeter;
* `injOn_rearTrack_shiftData` — embeddedness of the rear tracks of a shifted
  marking, from embeddedness for the curve itself;
* `selInv_shiftData_of_tube` — the equivariance of the selected inverse with the
  hypothesis for the shifts discharged.
-/

noncomputable section

open Set Function MarkedSpace MarkedShift RearTrack

namespace RearTrackShiftInjective

/-! ### A periodic map injective on one fundamental interval -/

/-- **A periodic map injective on `[0,L)` is injective on every translate
`[a, a+L)`.** -/
theorem injOn_Ico_of_periodic {α : Type*} {f : ℝ → α} {L a : ℝ} (hL : 0 < L)
    (hper : Function.Periodic f L) (hinj : InjOn f (Ico (0:ℝ) L)) :
    InjOn f (Ico a (a + L)) := by
  have hreduce : ∀ x : ℝ, x - (⌊x / L⌋ : ℤ) * L ∈ Ico (0:ℝ) L := by
    intro x
    have hfr : x - (⌊x / L⌋ : ℤ) * L = L * Int.fract (x / L) := by
      rw [Int.fract]
      field_simp
    rw [hfr]
    constructor
    · exact mul_nonneg hL.le (Int.fract_nonneg _)
    · nlinarith [Int.fract_lt_one (x / L), Int.fract_nonneg (x / L)]
  intro x hx y hy hxy
  have hfx : f (x - (⌊x / L⌋ : ℤ) * L) = f x := hper.sub_int_mul_eq _
  have hfy : f (y - (⌊y / L⌋ : ℤ) * L) = f y := hper.sub_int_mul_eq _
  have heq : x - (⌊x / L⌋ : ℤ) * L = y - (⌊y / L⌋ : ℤ) * L :=
    hinj (hreduce x) (hreduce y) (by rw [hfx, hfy, hxy])
  set k : ℤ := ⌊x / L⌋ - ⌊y / L⌋ with hk
  have hxy' : x - y = (k : ℝ) * L := by push_cast [hk]; linarith
  have hlt : |x - y| < L := by
    rw [abs_lt]
    constructor
    · linarith [hx.1, hy.2]
    · linarith [hy.1, hx.2]
  have hkabs : |(k : ℝ)| * L < L := by
    rw [← abs_of_pos hL, ← abs_mul, abs_of_pos hL, ← hxy']
    exact hlt
  have hk1 : |(k : ℝ)| < 1 := by nlinarith [abs_nonneg ((k : ℝ))]
  have hk0 : k = 0 := by
    have h : ((|k| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
    have hk' : |k| < 1 := by exact_mod_cast h
    rcases abs_lt.mp hk' with ⟨h1, h2⟩
    omega
  rw [hk0] at hxy'
  simp at hxy'
  linarith

/-! ### The rear track of a closed curve is periodic -/

variable {c kmin dlt kap : ℝ} {p : Data} {Θ K dl : ℝ → ℝ}

/-- The unit tangent of the arclength parametrization is periodic with the
perimeter: it is the derivative of a periodic map. -/
theorem periodic_expTangent (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hX : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) (s : ℝ) :
    Complex.exp (Complex.I * (Θ (s + perim p) : ℂ)) = Complex.exp (Complex.I * (Θ s : ℂ)) := by
  have hper : Function.Periodic (ev p) (perim p) := periodic_ev hc hp
  have hinner : HasDerivAt (fun y : ℝ => y + perim p) 1 s := by
    simpa using (hasDerivAt_id s).add_const (perim p)
  have h1 : HasDerivAt (fun y => ev p (y + perim p))
      (Complex.exp (Complex.I * (Θ (s + perim p) : ℂ))) s := by
    simpa using (hX (s + perim p)).scomp s hinner
  have hfun : (fun y => ev p (y + perim p)) = ev p := funext fun y => hper y
  rw [hfun] at h1
  exact h1.unique (hX s)

/-- **The rear track of a member of the tube is periodic with the perimeter.** -/
theorem periodic_rearTrack (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hX : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hdper : Function.Periodic dl (perim p)) :
    Function.Periodic (rearTrack (ev p) Θ dl) (perim p) := by
  intro s
  have hev : ev p (s + perim p) = ev p s := periodic_ev hc hp s
  have hexp := periodic_expTangent hc hp hX s
  have hdl : dl (s + perim p) = dl s := hdper s
  have hsplit : ∀ y : ℝ, Complex.exp (Complex.I * ((rearAngle Θ dl y : ℝ) : ℂ))
      = Complex.exp (Complex.I * (Θ y : ℂ)) * Complex.exp (-(Complex.I * (dl y : ℂ))) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    simp [rearAngle, Complex.ofReal_sub]
    ring
  rw [rearTrack, rearTrack, hsplit, hsplit, hev, hexp, hdl]

/-! ### Embeddedness for a shifted marking -/

/-- **Embeddedness of the rear tracks is inherited by a shift of the
marking.**  If every admissible steering angle on `p` has an embedded rear
track, the same holds for the data of `p` marked at another point. -/
theorem injOn_rearTrack_shiftData (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hinjR : ∀ Θ' K' dl' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl' (perim p) →
      (∀ s, dl' s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl' (K' s - Real.sin (dl' s)) s) →
      InjOn (rearTrack (ev p) Θ' dl') (Ico 0 (perim p)))
    (b : ℝ) :
    ∀ Θ' K' dl' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (shiftData b p)) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl' (perim (shiftData b p)) →
      (∀ s, dl' s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl' (K' s - Real.sin (dl' s)) s) →
      InjOn (rearTrack (ev (shiftData b p)) Θ' dl') (Ico 0 (perim (shiftData b p))) := by
  intro Θ' K' dl' hX' hΘ' hdper' hdmem' hode'
  have hLpos : 0 < perim p := perim_pos hc hp
  set L : ℝ := perim p with hLdef
  set t : ℝ := b * L with htdef
  have hperimb : perim (shiftData b p) = L :=
    SelectedInverseShiftEquivariance.perim_shiftData hp b
  have hevb : ∀ s, ev (shiftData b p) s = ev p (s + t) := fun s =>
    SelectedInverseShiftEquivariance.ev_shiftData hp hLpos.ne' b s
  -- the data of `p` obtained by translating the parameter back
  set Θ : ℝ → ℝ := fun y => Θ' (y - t) with hΘdef
  set K : ℝ → ℝ := fun y => K' (y - t) with hKdef
  set dl : ℝ → ℝ := fun y => dl' (y - t) with hdldef
  have hshift : ∀ s : ℝ, HasDerivAt (fun y : ℝ => y - t) 1 s := fun s => by
    simpa using (hasDerivAt_id s).sub_const t
  have hX : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    have h : HasDerivAt (fun y => ev (shiftData b p) (y - t))
        (Complex.exp (Complex.I * (Θ' (s - t) : ℂ))) s := by
      simpa using (hX' (s - t)).scomp s (hshift s)
    have hfun : (fun y => ev (shiftData b p) (y - t)) = ev p := by
      funext y
      rw [hevb (y - t)]
      ring_nf
    rw [hfun] at h
    exact h
  have hΘ : ∀ s, HasDerivAt Θ (K s) s := fun s => by
    simpa [hΘdef, hKdef] using (hΘ' (s - t)).scomp s (hshift s)
  have hdper : Function.Periodic dl L := by
    intro s
    have h : s + L - t = s - t + L := by ring
    simp only [hdldef, h]
    have := hdper' (s - t)
    rwa [hperimb] at this
  have hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap) := fun s => hdmem' (s - t)
  have hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s := fun s => by
    simpa [hdldef, hKdef] using (hode' (s - t)).scomp s (hshift s)
  have hinj : InjOn (rearTrack (ev p) Θ dl) (Ico 0 L) :=
    hinjR Θ K dl hX hΘ hdper hdmem hode
  have hper : Function.Periodic (rearTrack (ev p) Θ dl) L :=
    periodic_rearTrack hc hp hX hdper
  have hinjt : InjOn (rearTrack (ev p) Θ dl) (Ico t (t + L)) :=
    injOn_Ico_of_periodic hLpos hper hinj
  have hkey : ∀ x : ℝ, rearTrack (ev (shiftData b p)) Θ' dl' x
      = rearTrack (ev p) Θ dl (x + t) := by
    intro x
    have h1 : Θ (x + t) = Θ' x := by simp [hΘdef]
    have h2 : dl (x + t) = dl' x := by simp [hdldef]
    simp only [rearTrack, rearAngle, hevb x, h1, h2]
  intro x hx y hy hxy
  rw [hperimb] at hx hy
  have hxt : x + t ∈ Ico t (t + L) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyt : y + t ∈ Ico t (t + L) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have := hinjt hxt hyt (by rw [← hkey, ← hkey]; exact hxy)
  linarith

/-! ### The equivariance of the selected inverse, with the shifts discharged -/

/-- **The selected inverse is equivariant for shifts of the marking, from
embeddedness of the rear tracks of the curve alone.**  The hypothesis of
`SelectedInverseShiftEquivariance.selInv_shiftData` on the shifted data is
supplied by `injOn_rearTrack_shiftData`. -/
theorem selInv_shiftData_of_tube (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl' (perim p) →
      (∀ s, dl' s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl' (K' s - Real.sin (dl' s)) s) →
      InjOn (rearTrack (ev p) Θ' dl') (Ico 0 (perim p)))
    (b : ℝ) :
    ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b p)
      = shiftData cc (SelectedInverseMap.selInv kap p) :=
  SelectedInverseShiftEquivariance.selInv_shiftData hc hkmin hkap1 hp hub hinjR b
    (injOn_rearTrack_shiftData (kap := kap) hc hp hinjR b)

end RearTrackShiftInjective
