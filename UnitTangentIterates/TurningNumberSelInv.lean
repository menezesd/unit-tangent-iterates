import Mathlib
import UnitTangentIterates.TurningNumberTube
import UnitTangentIterates.TurningNumberPath
import UnitTangentIterates.SelectedInverseRearOwnShiftSteering
import UnitTangentIterates.SmoothCircleShiftInstance
import UnitTangentIterates.SelectedInverseRearOwnMarked

/-!
# The shift bound for the marked selected inverses, with the global hypotheses produced

`SelectedInverseRearOwnShiftSteering.exists_steering_pathDistShift_selInv_le`
bounds the distance, modulo the marking, between the marked selected inverses of
the two ends of a normal path of fronts, with the steering data produced from
the curvature.  Three of its hypotheses are the global ones this project carries
throughout:

* `hinjR`, `hinjRq` — embeddedness of every rear track of the two ends;
* `hturn` — the turning number of the slices of the path.

All three are produced here from the curvature pinching together with the length
threshold `κ̂·L < 4π`:

* the turning number of a closed curve is quantized in `2π`
  (`TurningNumber.exists_int_total_curvature`), so a curvature pinched by
  `0 < kmin ≤ K ≤ κ̂` with `κ̂·L < 4π` forces the total turning to be exactly `2π`
  (`TurningNumber.turning_eq_two_pi_of_pinched`);
* the rear tracks of a member of the tube of turning number one are embedded
  (`TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short`).

`exists_pinched_pathDistShift_selInv_le` is the resulting statement.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace TurningNumberSelInv

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn

variable {V A : ℝ → ℝ → ℂ} {Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the steering data produced and the three global hypotheses
discharged.**  `SelectedInverseRearOwnShiftSteering.exists_steering_pathDistShift_selInv_le`
with `hinjR`, `hinjRq` and `hturn` replaced by the curvature pinching
`0 < kmin ≤ K̂ ≤ κ̂ < 1` of the slices and the length thresholds
`κ̂·L < 4π` for the two ends and for every slice. -/
theorem exists_pinched_pathDistShift_selInv_le {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq Md MP CK CP kminK : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hshortp : kh * perim p < 4 * Real.pi)
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hshortq : kh * perim q < 4 * Real.pi)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hkminK : 0 < kminK) (hKnlow : ∀ t σ, kminK ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPsmall : ∀ t, kh * P t < 4 * Real.pi)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
          ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
            0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
            (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            MarkedShift.pathDistShift (SelectedInverseMap.selInv kh p)
                (SelectedInverseMap.selInv kh q) ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    Differentiable.continuous fun u => (hA t u).differentiableAt
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi :=
    TurningNumberPath.turning_of_path_of_pinched hA hVper hAper hVcont hAcont hspeed hPpos
      hkminK (fun t s => by rw [hKeq t s]; exact hKnlow t _)
      (fun t s => by rw [hKeq t s]; exact hKnk t _) hPsmall
  exact SelectedInverseRearOwnShiftSteering.exists_steering_pathDistShift_selInv_le Γ hc hkmin
    hp hub
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hc hkmin hkh1 hp hub hshortp)
    hcq hkminq hq hubq
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hcq hkminq hkh1 hq hubq hshortq)
    hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hKeq hKnper hKdnper
    (fun t σ => le_trans hkminK.le (hKnlow t σ)) hKnk hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4

/-- **The marked path-distance bound for the two selected inverses, with the
steering data produced and the three global hypotheses discharged.**
`SelectedInverseRearOwnMarked.exists_steering_pathDist_selInv_le` — the bound
for the *marked* pseudodistance, valid when the front's marked point is at rest
along the path — with `hinjR`, `hinjRq` and `hturn` replaced by the curvature
pinching and the length thresholds.  The condition `∀ t, Γ.eta t 0 = 0` remains,
as there. -/
theorem exists_pinched_pathDist_selInv_le {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq Md MP CK CP kminK : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hshortp : kh * perim p < 4 * Real.pi)
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hshortq : kh * perim q < 4 * Real.pi)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hkminK : 0 < kminK) (hKnlow : ∀ t σ, kminK ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPsmall : ∀ t, kh * P t < 4 * Real.pi)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
            0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
            (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ t, Γ.eta t 0 = 0) →
            pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
              ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    Differentiable.continuous fun u => (hA t u).differentiableAt
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi :=
    TurningNumberPath.turning_of_path_of_pinched hA hVper hAper hVcont hAcont hspeed hPpos
      hkminK (fun t s => by rw [hKeq t s]; exact hKnlow t _)
      (fun t s => by rw [hKeq t s]; exact hKnk t _) hPsmall
  exact SelectedInverseRearOwnMarked.exists_steering_pathDist_selInv_le Γ hc hkmin hp hub
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hc hkmin hkh1 hp hub hshortp)
    hcq hkminq hq hubq
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hcq hkminq hkh1 hq hubq hshortq)
    hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hKeq hKnper hKdnper
    (fun t σ => le_trans hkminK.le (hKnlow t σ)) hKnk hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4

/-! ### The instance -/

open SmoothCircleShiftInstance MovingCircleProfile MovingCircleCurvature MovingCircle
  MovingCircleNormalized SelectedInverseCircle SelectedInverseTubeCircle

/-- The radius of the dilating circle is at most `2`, since `sin A ≥ 1/2`. -/
theorem rad_le_two (t : ℝ) : rad t ≤ 2 := by
  have h := sA_ge t
  have hpos := sA_pos t
  rw [rad, div_le_iff₀ hpos]
  linarith

/-- The length threshold `κ̂·L < 4π` holds along the dilation of a circle. -/
theorem circle_short (t : ℝ) :
    Real.sin (Real.pi / 4) * (2 * Real.pi * rad t) < 4 * Real.pi := by
  have hpi := Real.pi_pos
  have hrad := rad_le_two t
  have hrpos := rad_pos t
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : Real.sqrt 2 < 2 := by nlinarith
  rw [Real.sin_pi_div_four]
  have hrewrite : Real.sqrt 2 / 2 * (2 * Real.pi * rad t) = Real.sqrt 2 * (Real.pi * rad t) := by
    ring
  rw [hrewrite]
  have h1 : Real.sqrt 2 * (Real.pi * rad t) ≤ Real.sqrt 2 * (Real.pi * 2) := by
    have : Real.pi * rad t ≤ Real.pi * 2 := by nlinarith
    nlinarith
  nlinarith

/-- **The hypotheses of `exists_pinched_pathDistShift_selInv_le` are
consistent.**  They hold for the smooth dilation of a circle of
`SmoothCircleShiftInstance.lean`: the curvature of its slices is pinched by
`1/2 ≤ K̂ ≤ sin(π/4)` and the length threshold `sin(π/4)·L < 4π` holds at every
time, so the embeddedness of the rear tracks and the turning number of the
slices are produced rather than assumed. -/
theorem circlePath_pinched_instance :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (Real.sin (Real.pi / 4)))) ∧
      (∀ t σ, HasDerivAt (dn t) (Pp t * (Kk t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / Pp t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ (C : ℝ) (Phi : ℝ → ℝ → ℝ),
        (∀ u, Phi 0 u
          = perim (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
              (circleData (rad 0))) * u) ∧
        ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
          0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
          (∀ u, HasDerivAt (Phi 1) (dPhi u) u) →
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
                (circleData (rad 1))).1
                (Phi 1 u / perim (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
                  (circleData (rad 1))))) →
          MarkedShift.pathDistShift
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 0)))
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 1)))
            ≤ C * cost circlePath := by
  have hpi := Real.pi_pos
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    SecondOrderBounds.exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CKb, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    SecondOrderBounds.exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  have htube : ∀ t : ℝ, IsTubeMember (2 * Real.pi * rad t) (1 / rad t) (4 * rad t)
      (circleData (rad t)) := fun t => circleData_mem_tube (rad_pos t)
  have hcurv : ∀ t u, ((starRingEnd ℂ) ((circleData (rad t)).2.1 u)
      * (circleData (rad t)).2.2 u).im
      ≤ Real.sin (Real.pi / 4) * ‖(circleData (rad t)).2.1 u‖ ^ 3 := by
    intro t u
    have h := SelectedInverseTubeCircle.circleData_curvature_le (rad_pos t) u
    have hle : 1 / rad t ≤ Real.sin (Real.pi / 4) := by
      rw [rad, one_div_one_div]
      exact sA_le t
    have hnn : (0 : ℝ) ≤ ‖(circleData (rad t)).2.1 u‖ ^ 3 := by positivity
    nlinarith
  have hshort : ∀ t : ℝ,
      Real.sin (Real.pi / 4) * perim (circleData (rad t)) < 4 * Real.pi := by
    intro t
    rw [perim_circleData (rad_pos t)]
    exact circle_short t
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    exists_pinched_pathDistShift_selInv_le
      (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (Pd := Ppd) (V := Vc) (A := Ac)
      (Kn := Kk) (Kdn := fun t _ => sAd t)
      (Md := Md) (MP := 8 * Real.pi * Md) (Klip := Md) (Plip := 8 * Real.pi * Md)
      (CK := CKb) (CP := 16 * Real.pi * (CKb + 2 * Md ^ 2))
      (c := 2 * Real.pi * rad 0) (kmin := 1 / rad 0) (dlt := 4 * rad 0)
      (cq := 2 * Real.pi * rad 1) (kminq := 1 / rad 1) (dltq := 4 * rad 1)
      (kminK := 1 / 2)
      circlePath
      (by have := rad_pos 0; positivity) (by have := rad_pos 0; positivity)
      (htube 0) (hcurv 0) (hshort 0)
      (by have := rad_pos 1; positivity) (by have := rad_pos 1; positivity)
      (htube 1) (hcurv 1) (hshort 1)
      (by positivity) hsin4pos hsin4
      (fun t => by
        rw [Pp, le_div_iff₀ (sA_pos t)]
        nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
      (fun t => by
        rw [Pp, div_le_iff₀ (sA_pos t)]
        nlinarith [sA_ge t])
      hasDerivAt_Vc hasDerivAt_Ac
      (fun t => (continuous_const.mul continuous_normExp))
      norm_Vc
      (fun t u => by simp [periodic_normExp u])
      (fun t u => by simp [Vc, periodic_normExp u])
      (fun t u => by simp [Ac, periodic_normExp u])
      (fun t u => by
        have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
        rw [circlePath_nu, Vc]
        field_simp
        rw [Complex.I_sq]
        ring)
      curvOfPath_circlePath
      (fun t σ => rfl) (fun t σ => rfl)
      (by norm_num) (fun t σ => sA_ge t) (fun t σ => sA_le t)
      (fun t => by
        rw [Pp_eq_two_pi_mul_rad t]
        exact circle_short t)
      (fun t σ => hMd t) (abs_Ppd_le hMd)
      (fun a b σ => by
        simpa [Kk] using SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_sAd hMd a b)
      (fun a b => SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_Pp (abs_Ppd_le hMd) a b)
      (fun a b σ => by
        simpa [Kk] using
          SecondOrderBounds.abs_taylor_quadratic hasDerivAt_sAd hasDerivAt_sAdd hCK a b)
      (fun a b => SecondOrderBounds.abs_taylor_quadratic hasDerivAt_Pp hasDerivAt_Ppd
        (abs_Ppdd_le hMd hCK) a b)
      hCK0 (by positivity)
      (contDiff_Pp 4) (contDiff_Ppd 3)
      (by
        have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA :=
          contDiff_sA.of_le (by exact ENat.LEInfty.out)
        simpa [Kk, uncurry] using h.comp contDiff_fst)
      (by
        have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sAd :=
          contDiff_sAd.of_le (by exact ENat.LEInfty.out)
        simpa [uncurry] using h.comp contDiff_fst)
      (by
        have hfun : uncurry (frontOfPath circlePath.X Pp)
            = fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ)
                * Complex.exp (((2 * Real.pi * (p.2 / Pp p.1) : ℝ) : ℂ) * Complex.I) := by
          funext p
          rw [uncurry, frontOfPath, circlePath_X, normExp_eq]
        rw [hfun]
        have hr : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ) :=
          contDiff_ofReal.comp (contDiff_rad.comp contDiff_fst)
        have hP : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => Pp p.1 :=
          (contDiff_Pp 4).comp contDiff_fst
        have harg : ContDiff ℝ (4 : ℕ)
            fun p : ℝ × ℝ => ((2 * Real.pi * (p.2 / Pp p.1) : ℝ) : ℂ) * Complex.I := by
          have hq : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => (2 * Real.pi * (p.2 / Pp p.1) : ℝ) :=
            contDiff_const.mul (contDiff_snd.div hP (fun p => (Pp_pos p.1).ne'))
          exact (contDiff_ofReal.comp hq).mul contDiff_const
        exact hr.mul
          (((Complex.contDiff_exp (𝕜 := ℂ) (n := (4 : ℕ))).restrict_scalars ℝ).comp harg))
      (by
        have hfun : uncurry (angleOfPath Vc Ac Pp)
            = fun p : ℝ × ℝ => Real.pi / 2 + p.2 * sA p.1 := by
          funext p
          rw [uncurry, angleOfPath_circlePath]
        rw [hfun]
        have h : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) sA :=
          contDiff_sA.of_le (by exact ENat.LEInfty.out)
        exact contDiff_const.add (contDiff_snd.mul (h.comp contDiff_fst)))
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨EF, -, -, Phi, hPhi0, -, hPhi⟩ := hrest
  exact ⟨_, Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp =>
    hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp⟩

end TurningNumberSelInv
