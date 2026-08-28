import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.MarkedRearOwnFloorFree

/-!
# The selected inverse map on the floor-free tube
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseMap

/-- **The selected inverse of a member of the floor-free tube is its marked
selected inverse.**  In particular the fallback branch of `selInv` — where it
returns its argument — is never taken on the tube, so `selInv kap` really is the
paper's rear map `𝔅` there. -/
theorem isMarkedSelectedInverse_selInv_floor_free {c dlt kap : ℝ} (hc : 0 < c)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    IsMarkedSelectedInverse kap p (selInv kap p) := by
  have hex : ∃ q, IsMarkedSelectedInverse kap p q := by
    obtain ⟨q, Θ, K, dl, sf, dR, hX, hΘ, hKlow, hKhigh, hdper, hdmem, hode, hsfinv, hdRpos,
      hmem, hperim, hoval, hqub, hrange, hev, -⟩ :=
      SelectedInverseRearOwn.exists_marked_rearOwn_floor_free hc hkap1 hp hub hinjR
    exact ⟨q, ⟨perim q, 0, dR, hmem⟩,
      Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, hperim, hev⟩
  rw [selInv, dif_pos hex]
  exact hex.choose_spec

/-- **The same, with embeddedness of the rear track discharged.**  The only
remaining geometric input is that some tangent-angle lift of the front turns by
`2π` over one period — the statement that the front is a convex closed curve of
total turning `2π`. -/
theorem isMarkedSelectedInverse_selInv_of_turning {c dlt kap : ℝ} (hc : 0 < c)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta' (K' s) s) ∧
      (∀ s, Theta' (s + perim p) = Theta' s + 2 * Real.pi)) :
    IsMarkedSelectedInverse kap p (selInv kap p) :=
  isMarkedSelectedInverse_selInv_floor_free hc hkap1 hp hub
    (RearTrackEmbedded.injOn_rearTrack_of_tube_floor_free hc hkap0 hkap1 hp hub hturn)

/-- **The rear map is into the tube.**  The rear of a member of the floor-free
tube is a member of a floor-free tube, with its own speed and chord-arc
constants. -/
theorem exists_tubeMember_selInv {c dlt kap : ℝ} (hc : 0 < c)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta' (K' s) s) ∧
      (∀ s, Theta' (s + perim p) = Theta' s + 2 * Real.pi)) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (selInv kap p)) 0 dR (selInv kap p) := by
  obtain ⟨q, Θ, K, dl, sf, dR, hX, hΘ, hKlow, hKhigh, hdper, hdmem, hode, hsfinv, hdRpos,
    hmem, hperim, hoval, hqub, hrange, hev, -⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn_floor_free hc hkap1 hp hub
      (RearTrackEmbedded.injOn_rearTrack_of_tube_floor_free hc hkap0 hkap1 hp hub hturn)
  have hq : IsMarkedSelectedInverse kap p q :=
    ⟨⟨perim q, 0, dR, hmem⟩, Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, hperim, hev⟩
  have heq : q = selInv kap p :=
    eq_selInv_of_isMarkedSelectedInverse hc hkap0 hkap1 hp hq
  exact ⟨dR, hdRpos, by rw [← heq]; exact hmem⟩

end SelectedInverseMap
