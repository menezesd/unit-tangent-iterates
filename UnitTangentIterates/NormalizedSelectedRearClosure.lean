import Mathlib
import UnitTangentIterates.MarkedTopology
import UnitTangentIterates.SelectedRear
import UnitTangentIterates.RearDependence
import UnitTangentIterates.HairpinLimit
import UnitTangentIterates.RearRegularity
import UnitTangentIterates.MarkedSpaceChord
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.UnitTangentSpeed

/-!
# Closure of normalized selected rears

This module isolates the period-one ODE argument used when a sequence of
marked curves converges in `MarkedTopology.MarkedC2Tendsto`.  Working on the
fixed normalized period avoids comparing tangent-angle lifts or varying
arclength periods.
-/

noncomputable section

open Set Function Filter Topology Real

namespace NormalizedSelectedRearClosure

/-- A reconstructed rear track is globally `1`-Lipschitz in front arclength.
Its derivative is `cos delta * exp(i Psi)`, whose norm is at most one. -/
theorem norm_rearTrack_sub_le
    {F : ℝ → ℂ} {Theta delta K : ℝ → ℝ}
    (hF : ∀ s, HasDerivAt F
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (K s) s)
    (hdelta : ∀ s, HasDerivAt delta
      (K s - Real.sin (delta s)) s) (x y : ℝ) :
    ‖RearTrack.rearTrack F Theta delta x -
      RearTrack.rearTrack F Theta delta y‖ ≤ |x - y| := by
  have hd : ∀ s, HasDerivAt (RearTrack.rearTrack F Theta delta)
      ((Real.cos (delta s) : ℂ) *
        Complex.exp (Complex.I * (RearTrack.rearAngle Theta delta s : ℂ))) s :=
    fun s => RearTrack.hasDerivAt_rearTrack (hF s) (hTheta s) (hdelta s)
  have hdiff : ∀ s ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (RearTrack.rearTrack F Theta delta) s :=
    fun s _ => (hd s).differentiableAt
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ‖deriv (RearTrack.rearTrack F Theta delta) s‖ ≤ 1 := by
    intro s _
    have h0 : (Complex.I * (RearTrack.rearAngle Theta delta s : ℂ)).re = 0 := by
      simp
    rw [(hd s).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, h0, Real.exp_zero, mul_one]
    exact abs_cos_le_one (delta s)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- Passing from front arclength to each rear's own arclength costs only the
inverse-coordinate error, because the limiting rear track is `1`-Lipschitz. -/
theorem norm_rearOwn_sub_le
    {F FN : ℝ → ℂ} {Theta ThetaN delta deltaN K : ℝ → ℝ}
    {sf sfN : ℝ → ℝ} {eTrack eInv : ℝ}
    (hF : ∀ s, HasDerivAt F
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (K s) s)
    (hdelta : ∀ s, HasDerivAt delta
      (K s - Real.sin (delta s)) s)
    (htrack : ∀ s, ‖RearTrack.rearTrack FN ThetaN deltaN s -
      RearTrack.rearTrack F Theta delta s‖ ≤ eTrack)
    (hsf : ∀ x, |sfN x - sf x| ≤ eInv) (x : ℝ) :
    ‖RearTrack.rearTrack FN ThetaN deltaN (sfN x) -
      RearTrack.rearTrack F Theta delta (sf x)‖ ≤ eTrack + eInv := by
  calc
    ‖RearTrack.rearTrack FN ThetaN deltaN (sfN x) -
        RearTrack.rearTrack F Theta delta (sf x)‖
      ≤ ‖RearTrack.rearTrack FN ThetaN deltaN (sfN x) -
          RearTrack.rearTrack F Theta delta (sfN x)‖ +
        ‖RearTrack.rearTrack F Theta delta (sfN x) -
          RearTrack.rearTrack F Theta delta (sf x)‖ := by
          simpa [dist_eq_norm] using dist_triangle
            (RearTrack.rearTrack FN ThetaN deltaN (sfN x))
            (RearTrack.rearTrack F Theta delta (sfN x))
            (RearTrack.rearTrack F Theta delta (sf x))
    _ ≤ eTrack + eInv := add_le_add (htrack (sfN x))
      ((norm_rearTrack_sub_le hF hTheta hdelta (sfN x) (sf x)).trans (hsf x))

/-- A selected steering solution for a normalized curvature of period one. -/
structure SteeringData (kap : ℝ) where
  K : ℝ → ℝ
  delta : ℝ → ℝ
  K_periodic : Periodic K 1
  delta_periodic : Periodic delta 1
  delta_mem : ∀ u, delta u ∈ Icc 0 (Real.arcsin kap)
  steering : ∀ u, HasDerivAt delta (K u - Real.sin (delta u)) u

/-- The selected steering ODE supplies the regularity gain at the limit.  No
convergence of derivatives of the steering angles is required: the limiting
ODE itself bootstraps the rear tangent angle. -/
theorem rear_contDiff_of_steeringData
    {kap : ℝ} (d : SteeringData kap) {Theta : ℝ → ℝ} {n : ℕ}
    (hTheta : ContDiff ℝ (n : ℕ) Theta)
    (hTheta' : ∀ s, HasDerivAt Theta (d.K s) s) :
    ContDiff ℝ (n + 2 : ℕ)
      (fun x => ∫ t in (0 : ℝ)..x,
        Complex.exp (((Theta t - d.delta t : ℝ) : ℂ) * Complex.I)) := by
  have hPsi : ∀ s, HasDerivAt (fun t => Theta t - d.delta t)
      (Real.sin (Theta s - (Theta s - d.delta s))) s := by
    intro s
    convert (hTheta' s).sub (d.steering s) using 1 <;> ring
  exact RearRegularity.rear_contDiff n hTheta hPsi

/-- Package a weakly convex regular periodic reconstruction as marked `Data`.
This is the zero-pinching specialization missing from the older strictly
positive selected-rear constructor. -/
theorem exists_nonnegative_rearData
    {Y : ℝ → ℂ} {theta k : ℝ → ℝ} {L kmax dlt : ℝ}
    (hL : 0 < L) (hYper : Periodic Y L)
    (hY : ∀ s, HasDerivAt Y
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (htheta : ∀ s, HasDerivAt theta (k s) s)
    (hkc : Continuous k) (hkper : Periodic k L)
    (hk0 : ∀ s, 0 ≤ k s) (hkmax : ∀ s, k s ≤ kmax)
    (hchord : ∀ x ∈ Icc (0 : ℝ) L, ∀ y ∈ Icc (0 : ℝ) L,
      dlt * min |x - y| (L - |x - y|) ≤ ‖Y x - Y y‖) :
    ∃ q : MarkedSpace.Data,
      MarkedSpace.IsTubeMember L 0 (dlt * L) q ∧
      MarkedSpace.perim q = L ∧ MarkedSpace.ev q = Y ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤
        kmax * ‖q.2.1 u‖ ^ 3 := by
  exact MarkedSpace.exists_tube_member_of_oval_chord hL hYper hY htheta
    hkc hkper hk0 hkmax hchord

/-- A packaged weakly convex rear satisfying the marked reconstruction data is
the canonical selected inverse.  Unlike `selInv_spec`, this identification
requires no positive curvature lower bound. -/
theorem packagedRear_eq_selInv
    {kap c kmin dlt cR kR dR : ℝ}
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p q : MarkedSpace.Data}
    (hp : MarkedSpace.IsTubeMember c kmin dlt p)
    (hqmem : MarkedSpace.IsTubeMember cR kR dR q)
    {Theta K delta sf : ℝ → ℝ}
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (K s) s)
    (hdeltaPer : Periodic delta (MarkedSpace.perim p))
    (hdeltaMem : ∀ s, delta s ∈ Icc 0 (Real.arcsin kap))
    (hdelta : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hsf : ∀ x, RearTrack.rearArclength delta (sf x) = x)
    (hperim : MarkedSpace.perim q =
      RearTrack.rearArclength delta (MarkedSpace.perim p))
    (hrear : ∀ x, MarkedSpace.ev q x =
      RearTrack.rearTrack (MarkedSpace.ev p) Theta delta (sf x)) :
    q = SelectedInverseMap.selInv kap p := by
  apply SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse hc hkap0 hkap1 hp
  exact ⟨⟨cR, kR, dR, hqmem⟩, Theta, K, delta, sf, hfront, hTheta,
    hdeltaPer, hdeltaMem, hdelta, hsf, hperim, hrear⟩

/-- Standalone regularity and strictness conclusion for one exact consecutive
pair.  The selected steering ODE gives the rear one extra derivative, while
nonnegative curvature of the next unit-tangent track forces a nonnegative,
nontrivial periodic rear curvature to be strictly positive. -/
theorem rear_regular_and_strict
    {kap L : ℝ} (d : SteeringData kap) {Theta k k' : ℝ → ℝ}
    (hL : 0 < L) (hThetaC1 : ContDiff ℝ (1 : ℕ) Theta)
    (hTheta : ∀ s, HasDerivAt Theta (d.K s) s)
    (hkper : Periodic k L) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk0 : ∀ s, 0 ≤ k s)
    (hnext : ∀ s,
      0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hkne : ∃ s, k s ≠ 0) :
    (∀ s, 0 < k s) ∧
    ContDiff ℝ (3 : ℕ)
      (fun x => ∫ t in (0 : ℝ)..x,
        Complex.exp (((Theta t - d.delta t : ℝ) : ℂ) * Complex.I)) := by
  refine ⟨UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg
    hL hkper hk hk0 hnext hkne, ?_⟩
  simpa using rear_contDiff_of_steeringData d hThetaC1 hTheta

/-- Quantitative continuity of normalized selected steering.  This is the
common-period form needed after `MarkedC2Tendsto` has transported all slices to
the normalized parameter. -/
theorem steering_sup_dist_le
    {kap eps : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (a b : SteeringData kap)
    (hK : ∀ u, |a.K u - b.K u| ≤ eps) :
    ∀ u, |a.delta u - b.delta u| ≤
      eps / Real.sqrt (1 - kap ^ 2) := by
  exact SelectedRear.steering_sup_dist_le one_pos hkap1 hkap0
    a.steering b.steering a.delta_periodic b.delta_periodic
    a.delta_mem b.delta_mem hK

/-- A global uniform inverse estimate.  It is the uniform version of the
pointwise estimate used in `HairpinLimit.tendsto_inverse_points`; no compactness
or subsequence extraction is needed. -/
theorem inverse_sup_dist_le
    {A AN sf sfN : ℝ → ℝ} {m eps : ℝ}
    (hm : 0 < m)
    (hslope : ∀ x y, x ≤ y → m * (y - x) ≤ A y - A x)
    (hclose : ∀ y, |AN y - A y| ≤ eps)
    (hinv : ∀ x, A (sf x) = x)
    (hinvN : ∀ x, AN (sfN x) = x) :
    ∀ x, |sfN x - sf x| ≤ eps / m := by
  intro x
  have hA : |A (sfN x) - A (sf x)| ≤ eps := by
    calc
      |A (sfN x) - A (sf x)| = |A (sfN x) - AN (sfN x)| := by
        rw [hinv x, hinvN x]
      _ = |AN (sfN x) - A (sfN x)| := abs_sub_comm _ _
      _ ≤ eps := hclose (sfN x)
  have hmetric : m * |sfN x - sf x| ≤ |A (sfN x) - A (sf x)| := by
    rcases le_total (sfN x) (sf x) with h | h
    · have hs := hslope (sfN x) (sf x) h
      have hmono : A (sfN x) ≤ A (sf x) := by nlinarith [hm]
      rw [abs_of_nonpos (sub_nonpos.mpr h),
        abs_of_nonpos (sub_nonpos.mpr hmono)]
      nlinarith
    · have hs := hslope (sf x) (sfN x) h
      have hmono : A (sf x) ≤ A (sfN x) := by nlinarith [hm]
      rw [abs_of_nonneg (sub_nonneg.mpr h),
        abs_of_nonneg (sub_nonneg.mpr hmono)]
      nlinarith
  rw [le_div_iff₀ hm, mul_comm]
  exact hmetric.trans hA

/-- The quantitative selected-rear closure interface.  Its fields are exactly
the outputs of normalized steering stability, primitive integration, inverse
stability, and `RearDependence.rear_depends_continuously`. -/
structure ClosureEstimate (kap epsK epsTheta epsFront epsPrimitive m : ℝ) where
  steering : ℝ → ℝ
  rearParameter : ℝ → ℝ
  steering_bound : ∀ u,
    |steering u| ≤ epsK / Real.sqrt (1 - kap ^ 2)
  rearParameter_bound : ∀ u, |rearParameter u| ≤ epsPrimitive / m
  rear_position_bound : ℝ → ℝ
  rear_tangent_bound : ℝ → ℝ
  rear_curvature_bound : ℝ → ℝ
  position_le : ∀ u, rear_position_bound u ≤
    epsFront + (epsTheta + epsK / Real.sqrt (1 - kap ^ 2))
  tangent_le : ∀ u, rear_tangent_bound u ≤
    epsTheta + epsK / Real.sqrt (1 - kap ^ 2)
  curvature_le : ∀ u, rear_curvature_bound u ≤
    epsK / Real.sqrt (1 - kap ^ 2) / (1 - kap ^ 2)

/-- Quantitative closure of normalized selected rears.  This composes common-
period steering stability, rear-period/primitive control, uniform inverse
stability, and the reconstruction estimates of `RearDependence`. -/
theorem selectedRear_closure_bound
    {kap epsK epsTheta epsFront epsPrimitive m : ℝ}
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hm : 0 < m)
    {F FN : ℝ → ℂ} {Theta ThetaN : ℝ → ℝ}
    (d dN : SteeringData kap)
    (hK : ∀ u, |dN.K u - d.K u| ≤ epsK)
    (hTheta : ∀ u, |ThetaN u - Theta u| ≤ epsTheta)
    (hF : ∀ u, ‖FN u - F u‖ ≤ epsFront)
    {A AN sf sfN : ℝ → ℝ}
    (hAslope : ∀ x y, x ≤ y → m * (y - x) ≤ A y - A x)
    (hAclose : ∀ y, |AN y - A y| ≤ epsPrimitive)
    (hsf : ∀ x, A (sf x) = x) (hsfN : ∀ x, AN (sfN x) = x) :
    (∀ u, |dN.delta u - d.delta u| ≤
      epsK / Real.sqrt (1 - kap ^ 2)) ∧
    |AN 1 - A 1| ≤ epsPrimitive ∧
    (∀ x, |sfN x - sf x| ≤ epsPrimitive / m) ∧
    (∀ u, |RearTrack.rearAngle ThetaN dN.delta u -
      RearTrack.rearAngle Theta d.delta u| ≤
        epsTheta + epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ u, ‖Complex.exp
          (Complex.I * (RearTrack.rearAngle ThetaN dN.delta u : ℂ)) -
        Complex.exp
          (Complex.I * (RearTrack.rearAngle Theta d.delta u : ℂ))‖ ≤
        epsTheta + epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ u, ‖RearTrack.rearTrack FN ThetaN dN.delta u -
        RearTrack.rearTrack F Theta d.delta u‖ ≤
        epsFront + (epsTheta + epsK / Real.sqrt (1 - kap ^ 2))) ∧
    (∀ u, |Real.cos (dN.delta u) - Real.cos (d.delta u)| ≤
      epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ u, |Real.tan (dN.delta u) - Real.tan (d.delta u)| ≤
      epsK / Real.sqrt (1 - kap ^ 2) / (1 - kap ^ 2)) := by
  have hsteer : ∀ u, |dN.delta u - d.delta u| ≤
      epsK / Real.sqrt (1 - kap ^ 2) :=
    steering_sup_dist_le hkap0 hkap1 dN d hK
  have hrear := RearDependence.rear_depends_continuously one_pos hkap0 hkap1
    dN.steering d.steering dN.delta_periodic d.delta_periodic
    dN.delta_mem d.delta_mem hK hTheta hF
  refine ⟨hsteer, hAclose 1,
    inverse_sup_dist_le hm hAslope hAclose hsf hsfN, ?_⟩
  exact hrear.2

end NormalizedSelectedRearClosure
