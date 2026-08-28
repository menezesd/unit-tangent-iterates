import UnitTangentIterates.SelectedInverseMapFloorFree
import UnitTangentIterates.ChordUniform

/-!
# The selected inverse in an honest transformed tube

A selected rear does not preserve an arbitrary fixed positive perimeter lower
bound: its perimeter is the integral of `cos delta` and is generally smaller
than the front perimeter.  This module records the sharp uniform lower bound
that does follow from the selected strip, together with a uniform chord
constant obtained from the rear curvature ceiling.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Function Real MarkedSpace RearTrack ArclengthInverse SelectedInverseRearOwn

namespace SelectedInverseTransformedTube

/-- Uniform speed lower bound after one selected-rear step. -/
def rearSpeedLower (kh c : ℝ) : ℝ := Real.sqrt (1 - kh ^ 2) * c

/-- Uniform chord constant after one selected-rear step. -/
def rearChordLower (kh c : ℝ) : ℝ :=
  min (rearSpeedLower kh c / 2)
    (Real.pi / (6 * (kh / Real.sqrt (1 - kh ^ 2))))

/-- Construct the marked selected rear of a floor-free tube member and place
it in the explicit transformed tube.  Turning one and the upper curvature
barrier are stated explicitly because neither is a field of `IsTubeMember`.
-/
theorem exists_markedRear_mem_transformedTube
    {kh c dlt : ℝ} (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta' (K' s) s) ∧
      (∀ s, Theta' (s + perim p) = Theta' s + 2 * Real.pi)) :
    ∃ q : Data,
      SelectedInverseMap.IsMarkedSelectedInverse kh p q ∧
      IsTubeMember (rearSpeedLower kh c) 0 (rearChordLower kh c) q := by
  have hinjR := RearTrackEmbedded.injOn_rearTrack_of_tube_floor_free
    hc hkh0 hkh1 hp hub hturn
  obtain ⟨q, Theta, K, delta, sf, dR, hX, hTheta, hK0, hKkh,
      hdper, hdmem, hdode, hsfinv, hdR, hqmem, hqperim, hoval,
      hqub, hrange, hqrear, hqmark⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn_floor_free
      hc hkh1 hp hub hinjR
  have hPpos : 0 < perim p := perim_pos hc hp
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  have hdeltaC : Continuous delta :=
    Differentiable.continuous fun s => (hdode s).differentiableAt
  have hsfC : Continuous sf :=
    continuous_of_rightInverse hsqrt
      (fun s => hasDerivAt_rearArclength hdeltaC s)
      (fun s => Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2)
      hsfinv
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (delta s) :=
    fun s => Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hrearSpeed : rearSpeedLower kh c ≤ perim q := by
    rw [hqperim]
    apply le_trans _ (rearArclength_ge hdeltaC hcos hPpos.le)
    exact mul_le_mul_of_nonneg_left
      (by simpa [perim] using hp.speed_lb 0) hsqrt.le
  obtain ⟨s0, hs0⟩ := UnconditionalAssembly.arcCurv_nonzero hc hp
  have hKs0 : K s0 ≠ 0 := by
    rw [RearTrackEmbedded.curvature_eq_arcCurv hc hp hX hTheta s0]
    exact hs0
  have hkhpos : 0 < kh := lt_of_lt_of_le
    (lt_of_le_of_ne (hK0 s0) (Ne.symm hKs0)) (hKkh s0)
  have hrearPinch := LowCurvatureAssembly.selected_rear_curvature_pinched
    hPpos (le_refl (0 : ℝ)) hkh1 hdper hdode hdmem hK0
  let thetaR : ℝ → ℝ := fun x => rearAngle Theta delta (sf x)
  let kR : ℝ → ℝ := fun x => Real.tan (delta (sf x))
  have hqrearfun : ev q = fun x => rearTrack (ev p) Theta delta (sf x) :=
    funext hqrear
  have hqderiv : ∀ x, HasDerivAt (ev q)
      (Complex.exp (Complex.I * (thetaR x : ℂ))) x := by
    intro x
    rw [hqrearfun]
    exact hasDerivAt_rearOwnCurve hsqrt hdeltaC hcos hsfinv hX hTheta hdode x
  have hthetaR : ∀ x, HasDerivAt thetaR (kR x) x := by
    intro x
    exact hasDerivAt_rearOwnAngleSf hsqrt hdeltaC hcos hsfinv hTheta hdode x
  obtain ⟨Theta', K', hX', hTheta', hturn'⟩ := hturn
  have hturnTheta : ∀ s, Theta (s + perim p) = Theta s + 2 * Real.pi :=
    RearTrackEmbedded.turning_of_lift hX hX' hTheta hTheta' hturn'
  have hturnR : ∀ x, thetaR (x + perim q) = thetaR x + 2 * Real.pi := by
    intro x
    dsimp [thetaR]
    rw [hqperim, sf_add_rearPeriod hsqrt hdeltaC hcos hdper hsfinv]
    rw [rearAngle, rearAngle, hturnTheta, hdper]
    ring
  have hkR0 : ∀ x, 0 ≤ kR x := fun x => by
    simpa [kR] using (hrearPinch (sf x)).1
  have hkRle : ∀ x, kR x ≤ kh / Real.sqrt (1 - kh ^ 2) :=
    fun x => hrearPinch (sf x) |>.2
  have hrearCeiling : 0 < kh / Real.sqrt (1 - kh ^ 2) := by positivity
  have hqPpos : 0 < perim q := by
    rw [hqperim]
    exact rearPeriod_pos hPpos hsqrt hdeltaC hcos
  have hqderiv' : ∀ x, HasDerivAt (ev q)
      (Complex.exp ((thetaR x : ℂ) * Complex.I)) x := by
    intro x
    simpa [mul_comm] using hqderiv x
  have hchord := Marked.chord_of_tube_curvature_ceiling
    hqPpos hqmem hrearCeiling hqderiv' hthetaR hkR0 hkRle hturnR
  have hcoef : rearChordLower kh c ≤
      min (perim q / 2) (Real.pi / (6 * (kh / Real.sqrt (1 - kh ^ 2)))) := by
    apply min_le_min_right
    exact div_le_div_of_nonneg_right hrearSpeed (by norm_num)
  have hqtrans : IsTubeMember (rearSpeedLower kh c) 0
      (rearChordLower kh c) q :=
    { hasDerivAt_curve := hqmem.hasDerivAt_curve
      hasDerivAt_vel := hqmem.hasDerivAt_vel
      periodic := hqmem.periodic
      speed_const := hqmem.speed_const
      speed_lb := fun u => hrearSpeed.trans (hqmem.speed_lb u)
      curv_lb := hqmem.curv_lb
      chord := by
        intro u hu v hv
        exact (mul_le_mul_of_nonneg_right hcoef (ChordArc.cyc_nonneg hu hv)).trans
          (hchord u hu v hv) }
  refine ⟨q, ?_, hqtrans⟩
  exact ⟨⟨perim q, 0, dR, hqmem⟩, Theta, K, delta, sf,
    hX, hTheta, hdper, hdmem, hdode, hsfinv, hqperim, hqrear⟩

/-- Canonical-map form of `exists_markedRear_mem_transformedTube`. -/
theorem selInv_mem_transformedTube
    {kh c dlt : ℝ} (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta' (K' s) s) ∧
      (∀ s, Theta' (s + perim p) = Theta' s + 2 * Real.pi)) :
    IsTubeMember (rearSpeedLower kh c) 0 (rearChordLower kh c)
      (SelectedInverseMap.selInv kh p) := by
  obtain ⟨q, hq, hqmem⟩ :=
    exists_markedRear_mem_transformedTube hc hkh0 hkh1 hp hub hturn
  rw [← SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse
    hc hkh0 hkh1 hp hq]
  exact hqmem

end SelectedInverseTransformedTube
