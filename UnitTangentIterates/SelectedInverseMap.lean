import Mathlib
import UnitTangentIterates.SelectedInverseUnique

/-!
# The selected inverse as a single-valued map of marked curves

`SelectedInverseRearOwn.exists_marked_rearOwn` produces a marked selected
inverse of a member of the tube, and `SelectedInverseUnique.lean` shows that it
is unique.  This file packages the two into a **map** `selInv κ̂ : Data → Data`,
as the shadowing scheme of the paper requires: a curve, not a family of
choices.

* `IsMarkedSelectedInverse κ̂ p q` — the property characterizing the marked
  selected inverse: `q` is a marked curve which is the rear track of `p`,
  written in its own arclength and marked at `x = 0`, for some front data,
  some steering angle on the closed strip `[0, arcsin κ̂]` and some right
  inverse of the rear arclength;
* `IsMarkedSelectedInverse.unique` — the property determines `q`;
* `selInv` — the resulting map, defined by the property when it is satisfiable
  and by the identity otherwise;
* `isMarkedSelectedInverse_selInv` — for a member of the tube of curvature
  pinched by `0 < kmin ≤ K ≤ κ̂ < 1`, `selInv κ̂ p` has the property;
* `selInv_eq` — hence any curve with the property *is* `selInv κ̂ p`;
* `selInv_spec` — the geometry of the image: it is a member of the tube of
  curvature at least `kmin/√(1-kmin²)` and at most `κ̂/√(1-κ̂²)`, an oval, and
  its unit-tangent transform retraces `p`.
-/

noncomputable section

open Set Function MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseMap

/-- **The marked selected inverse relation.**  `q` is the rear track of the
marked curve `p`, written in its own arclength and marked at `x = 0`. -/
def IsMarkedSelectedInverse (kap : ℝ) (p q : Data) : Prop :=
  (∃ c' k' d' : ℝ, IsTubeMember c' k' d' q) ∧
  ∃ Θ K dl sf : ℝ → ℝ,
    (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) ∧
    (∀ s, HasDerivAt Θ (K s) s) ∧
    Function.Periodic dl (perim p) ∧
    (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) ∧
    (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) ∧
    (∀ x, rearArclength dl (sf x) = x) ∧
    perim q = rearArclength dl (perim p) ∧
    (∀ x, ev q x = rearTrack (ev p) Θ dl (sf x))

/-- **The marked selected inverse is unique.** -/
theorem IsMarkedSelectedInverse.unique {c kmin dlt kap : ℝ} (hc : 0 < c) (hkap0 : 0 ≤ kap)
    (hkap1 : kap < 1) {p q₁ q₂ : Data} (hp : IsTubeMember c kmin dlt p)
    (h₁ : IsMarkedSelectedInverse kap p q₁) (h₂ : IsMarkedSelectedInverse kap p q₂) :
    q₁ = q₂ := by
  obtain ⟨⟨c₁, k₁, d₁, hq₁⟩, Θ₁, K₁, dl₁, sf₁, hX₁, hΘ₁, hdper₁, hdmem₁, hode₁, hsfinv₁,
    hperim₁, hev₁⟩ := h₁
  obtain ⟨⟨c₂, k₂, d₂, hq₂⟩, Θ₂, K₂, dl₂, sf₂, hX₂, hΘ₂, hdper₂, hdmem₂, hode₂, hsfinv₂,
    hperim₂, hev₂⟩ := h₂
  exact SelectedInverseUnique.marked_rearOwn_unique hc hkap0 hkap1 hp hq₁ hq₂ hX₁ hΘ₁ hdper₁
    hdmem₁ hode₁ hsfinv₁ hperim₁ hev₁ hX₂ hΘ₂ hdper₂ hdmem₂ hode₂ hsfinv₂ hperim₂ hev₂

open Classical in
/-- **The selected inverse as a map of marked curves.**  Where the marked
selected inverse exists it is the image; elsewhere the map is the identity (the
value there is irrelevant: every statement about `selInv` below assumes the
curve to be an admissible member of the tube). -/
def selInv (kap : ℝ) (p : Data) : Data :=
  if h : ∃ q, IsMarkedSelectedInverse kap p q then h.choose else p

/-- **Weak closed-strip identification of the canonical selected inverse.**
No positive curvature lower bound is needed here.  Once a marked rear has been
constructed from the closed-strip steering data, uniqueness identifies it
with `selInv`; in particular the fallback branch of `selInv` is impossible. -/
theorem eq_selInv_of_isMarkedSelectedInverse {c kmin dlt kap : ℝ}
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p q : Data} (hp : IsTubeMember c kmin dlt p)
    (hq : IsMarkedSelectedInverse kap p q) :
    q = selInv kap p := by
  have hex : ∃ r, IsMarkedSelectedInverse kap p r := ⟨q, hq⟩
  rw [selInv, dif_pos hex]
  exact hq.unique hc hkap0 hkap1 hp hex.choose_spec

/-- Transfer any weak-convex tube certificate for a constructed marked rear
to the canonical selected inverse.  This is the zero-pinching replacement for
the final identification step of `selInv_spec`; it deliberately assumes
neither strict curvature nor injectivity of every steering solution. -/
theorem selInv_spec_of_markedRear {c kmin dlt kap cR kR dR : ℝ}
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p q : Data} (hp : IsTubeMember c kmin dlt p)
    (hq : IsMarkedSelectedInverse kap p q)
    (hqmem : IsTubeMember cR kR dR q) :
    IsTubeMember cR kR dR (selInv kap p) := by
  rw [← eq_selInv_of_isMarkedSelectedInverse hc hkap0 hkap1 hp hq]
  exact hqmem

/-- **The selected inverse of an admissible marked curve is its marked selected
inverse.** -/
theorem isMarkedSelectedInverse_selInv {c kmin dlt kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c kmin dlt p)
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
      SelectedInverseRearOwn.exists_marked_rearOwn hc hkmin hkap1 hp hub hinjR
    exact ⟨q, ⟨perim q, kmin / Real.sqrt (1 - kmin ^ 2), dR, hmem⟩,
      Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, hperim, hev⟩
  rw [selInv, dif_pos hex]
  exact hex.choose_spec

/-- **Any marked selected inverse of an admissible marked curve is the value of
the map.** -/
theorem selInv_eq {c kmin dlt kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    {p q : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p)))
    (hq : IsMarkedSelectedInverse kap p q) : q = selInv kap p := by
  have hkap0 : 0 ≤ kap := by
    have h := le_trans (hp.curv_lb 0) (hub 0)
    have hn : 0 < ‖p.2.1 0‖ ^ 3 := by
      have : 0 < ‖p.2.1 0‖ := lt_of_lt_of_le hc (hp.speed_lb 0)
      positivity
    nlinarith [hkmin]
  exact hq.unique hc hkap0 hkap1 hp
    (isMarkedSelectedInverse_selInv hc hkmin hkap1 hp hub hinjR)

/-- **The geometry of the selected inverse.**  For a member `p` of the tube of
curvature pinched by `0 < kmin ≤ K ≤ κ̂ < 1`, the image `selInv κ̂ p` is a member
of the tube of curvature at least `kmin/√(1-kmin²)` and at most `κ̂/√(1-κ̂²)`, an
oval, and its unit-tangent transform retraces `p`. -/
theorem selInv_spec {c kmin dlt kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (selInv kap p)) (kmin / Real.sqrt (1 - kmin ^ 2)) dR
        (selInv kap p) ∧
      MainTheoremConditional.IsOval (ev (selInv kap p)) ∧
      (∀ u, ((starRingEnd ℂ) ((selInv kap p).2.1 u) * (selInv kap p).2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) * ‖(selInv kap p).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (selInv kap p))) = range (ev p) := by
  obtain ⟨q, Θ, K, dl, sf, dR, hX, hΘ, hKlow, hKhigh, hdper, hdmem, hode, hsfinv, hdRpos,
    hmem, hperim, hoval, hqub, hrange, hev, -⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn hc hkmin hkap1 hp hub hinjR
  have hqeq : q = selInv kap p :=
    selInv_eq hc hkmin hkap1 hp hub hinjR
      ⟨⟨perim q, kmin / Real.sqrt (1 - kmin ^ 2), dR, hmem⟩,
        Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, hperim, hev⟩
  rw [← hqeq]
  exact ⟨dR, hdRpos, hmem, hoval, hqub, hrange⟩

end SelectedInverseMap
