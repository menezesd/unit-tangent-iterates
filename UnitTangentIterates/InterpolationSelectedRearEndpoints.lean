import Mathlib
import UnitTangentIterates.InterpolationSelectedRearClosing
import UnitTangentIterates.SelectedInverseMap

/-!
# Identification of interpolation rear endpoints with marked selected inverses

The selected inverse is unique as a marked curve.  Consequently an endpoint
rear written in its own arclength is exactly `selInv`, provided its marking is
the affine marking of one rear period.  This is the precise endpoint bridge
needed after the qualitative interpolation and closing constructions.
-/

noncomputable section

open Function Set Complex MarkedSpace RearTrack

namespace InterpolationSelectedRearEndpoints

open RearOwnArclength SelectedInverseMap

/-- **An affinely marked rear endpoint is the marked selected inverse.**

The existence of a marked selected inverse is supplied internally by
`SelectedInverseMap.selInv_eq` (through
`SelectedInverseRearOwn.exists_marked_rearOwn`).  The hypotheses below only
say that the proposed endpoint datum is the same rear track, in its own
arclength, with the canonical affine marking. -/
theorem marked_rearEndpoint_eq_selInv
    {p q : Data} {F : ℝ → ℂ} {Theta K delta sf : ℝ → ℝ}
    {c kmin dlt cq kminq dltq kap P : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hq : IsTubeMember cq kminq dltq q)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im
      ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Theta' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta' s : ℂ))) s) →
      (∀ s, HasDerivAt Theta' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Theta' dl) (Ico 0 (perim p)))
    (hP : 0 < P) (hperimP : perim p = P) (hevP : ev p = F)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (K s) s)
    (hdper : Function.Periodic delta P)
    (hdmem : ∀ s, delta s ∈ Icc 0 (Real.arcsin kap))
    (hsteer : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hsfinv : ∀ x, rearArclength delta (sf x) = x)
    (hperimQ : perim q = rearArclength delta P)
    (hmark : ∀ u, q.1 u =
      rearTrack F Theta delta (sf (rearArclength delta P * u))) :
    q = selInv kap p := by
  have hkap0 : 0 ≤ kap := by
    exact Real.arcsin_nonneg.mp (le_trans (hdmem 0).1 (hdmem 0).2)
  have hdeltaC : Continuous delta :=
    Differentiable.continuous fun s => (hsteer s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hroot : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hQpos : 0 < rearArclength delta P :=
    SelectedInverseRearOwn.rearPeriod_pos hP hroot hdeltaC hcos
  have hevQ : ∀ x, ev q x = rearTrack (ev p) Theta delta (sf x) := by
    intro x
    rw [ev, hmark, hperimQ, hevP]
    have hQne : rearArclength delta P ≠ 0 := hQpos.ne'
    have hx : rearArclength delta P * (x / rearArclength delta P) = x := by
      field_simp
    rw [hx]
  have hmarked : IsMarkedSelectedInverse kap p q := by
    refine ⟨⟨cq, kminq, dltq, hq⟩, Theta, K, delta, sf, ?_, hTheta, ?_, hdmem,
      hsteer, hsfinv, (by rw [hperimP]; exact hperimQ), hevQ⟩
    · intro s
      rw [hevP]
      exact hF s
    · rw [hperimP]
      exact hdper
  exact selInv_eq hc hkmin hkap1 hp hub hinjR hmarked

end InterpolationSelectedRearEndpoints
