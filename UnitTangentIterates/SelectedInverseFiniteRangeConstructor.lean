import UnitTangentIterates.PullbackUnitTangentRangeOrbit
import UnitTangentIterates.SelectedInverseMapFloorFree

/-!
# Finite selected-inverse range identities

This module constructs the finite range premise used by
`selectedInverse_orbitRange_of_finiteRange`.  At a positive-speed floor-free
tube member, the only geometric inputs are the selected-strip curvature upper
bound and a turning-one tangent-angle lift.  The floor-free rear construction
then supplies a marked rear whose unit-tangent image is the front, and
uniqueness identifies that rear with `selInv`.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseFiniteRangeConstructor

/-- A floor-free front with curvature in the selected strip and turning number
one is retraced by the unit-tangent image of its canonical selected inverse. -/
theorem range_ev_eq_unitTangent_selInv_of_turning
    {c dlt kh : ℝ} (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (K s) s) ∧
      (∀ s, Theta (s + perim p) = Theta s + 2 * Real.pi)) :
    range (ev p) = range (UnitTangent.unitTangentMap
      (ev (SelectedInverseMap.selInv kh p))) := by
  have hinj : ∀ Theta K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) →
      (∀ s, HasDerivAt Theta (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Theta dl) (Ico 0 (perim p)) :=
    RearTrackEmbedded.injOn_rearTrack_of_tube_floor_free
      hc hkh0 hkh1 hp hub hturn
  obtain ⟨q, Theta, K, dl, sf, dR, hX, hTheta, _hKlow, _hKhigh,
      hdper, hdmem, hode, hsfinv, _hdRpos, hqmem, hperim, _hoval,
      _hqub, hrange, hev, _hmark⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn_floor_free
      hc hkh1 hp hub hinj
  have hmarked : SelectedInverseMap.IsMarkedSelectedInverse kh p q :=
    ⟨⟨perim q, 0, dR, hqmem⟩, Theta, K, dl, sf, hX, hTheta,
      hdper, hdmem, hode, hsfinv, hperim, hev⟩
  have hq : q = SelectedInverseMap.selInv kh p :=
    SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse
      hc hkh0 hkh1 hp hmarked
  rw [← hq]
  exact hrange.symm

/-- The finite range premise for every actual pullback front follows from
stagewise selected-strip and turning-one facts.  Combined with marked row
convergence, this yields the limiting unit-tangent range orbit directly. -/
theorem pullback_orbitRange_of_curvature_turning
    {kh : ℝ} {Q : ℕ → Data} {X : ℕ → Data}
    {c dlt : ℝ}
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hXmem : ∀ n, IsTubeMember c 0 dlt (X n))
    (hXlim : ∀ n,
      Tendsto (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n)
        atTop (nhds (X n)))
    (hub : ∀ n k u,
      ((starRingEnd ℂ)
          ((TubePullbackLimit.pullback
            (SelectedInverseMap.selInv kh) Q (n + 1) k).2.1 u) *
        (TubePullbackLimit.pullback
          (SelectedInverseMap.selInv kh) Q (n + 1) k).2.2 u).im ≤
      kh * ‖(TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q (n + 1) k).2.1 u‖ ^ 3)
    (hturn : ∀ n k, ∃ Theta K : ℝ → ℝ,
      (∀ s, HasDerivAt
        (ev (TubePullbackLimit.pullback
          (SelectedInverseMap.selInv kh) Q (n + 1) k))
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (K s) s) ∧
      (∀ s, Theta
          (s + perim (TubePullbackLimit.pullback
            (SelectedInverseMap.selInv kh) Q (n + 1) k)) =
        Theta s + 2 * Real.pi)) :
    ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
  apply PullbackUnitTangentRangeOrbit.selectedInverse_orbitRange_of_finiteRange
    hc hmem hXmem hXlim
  intro n k
  exact range_ev_eq_unitTangent_selInv_of_turning hc hkh0 hkh1
    (hmem (n + 1) k) (hub n k) (hturn n k)

end SelectedInverseFiniteRangeConstructor
