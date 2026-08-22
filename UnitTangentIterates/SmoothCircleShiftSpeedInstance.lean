import Mathlib
import UnitTangentIterates.SmoothCircleShiftInstance
import UnitTangentIterates.SelectedInverseRearOwnShiftSteeringSpeed
import UnitTangentIterates.SelectedInverseQuotientSpeed

/-!
# The shift bound with the constant fixed by the speed of the path is not vacuous

`SmoothCircleShiftInstance.circlePath_shift_instance` checks that the
hypotheses of the shift bound with the steering data produced are consistent,
on the smooth dilation of a circle.  This file runs the same check for the
version whose constant is fixed by the speed of the path
(`SelectedInverseRearOwnShiftSteeringSpeed.lean`): the only extra hypothesis is
a bound `M` for the cost density of the path, and every normal path has one
(`PathMetric.NormalPath.exists_bound_m`).

The conclusion is the bound with the **explicit uniform constant**
`SelectedInverseQuotientSpeed.selInvGaugeConst`, so the constant of the chain is
exhibited on a concrete path.

Main result: `circlePath_shift_instance_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SmoothCircleShiftSpeedInstance

open MovingCircleProfile MovingCircleCurvature MovingCircle MovingCircleNormalized
  FrontFromPath SelectedInverseCircle SelectedInverseTubeCircle SmoothCircleShiftInstance

/-- **The hypotheses of the shift bound with the constant fixed by the speed of
the path are consistent.**  They hold for the smooth dilation of a circle: the
family of circles of radius `1 / sin A(t)`, whose ends are the marked circles of
radius `√2` and `2`.  The cost density of that path is bounded by some `M`, the
selected steering data are produced from the curvature alone, and the two marked
selected inverses of the ends are at distance, modulo the marking, at most the
explicit uniform constant `selInvGaugeConst (2π) (4π) (sin(π/4)) M Q` times the
cost of the path. -/
theorem circlePath_shift_instance_speed :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ t, circlePath.m t ≤ M) ∧
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (Real.sin (Real.pi / 4)))) ∧
      (∀ t σ, HasDerivAt (dn t) (Pp t * (Kk t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / Pp t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
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
            ≤ SelectedInverseQuotientSpeed.selInvGaugeConst (2 * Real.pi) (4 * Real.pi)
                (Real.sin (Real.pi / 4)) M
                (rearArclength (δ 0) (Pp 0)) * cost circlePath := by
  obtain ⟨M, hM0, hM⟩ := circlePath.exists_bound_m
  refine ⟨M, hM0, hM, ?_⟩
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
  -- the tube data of the two ends
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
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    SelectedInverseRearOwnShiftSteeringSpeed.exists_steering_pathDistShift_selInv_le_speed
      (M := M) (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (Pd := Ppd) (V := Vc) (A := Ac)
      (Kn := Kk) (Kdn := fun t _ => sAd t)
      (Md := Md) (MP := 8 * Real.pi * Md) (Klip := Md) (Plip := 8 * Real.pi * Md)
      (CK := CKb) (CP := 16 * Real.pi * (CKb + 2 * Md ^ 2))
      (c := 2 * Real.pi * rad 0) (kmin := 1 / rad 0) (dlt := 4 * rad 0)
      (cq := 2 * Real.pi * rad 1) (kminq := 1 / rad 1) (dltq := 4 * rad 1)
      circlePath
      (by have := rad_pos 0; positivity) (by have := rad_pos 0; positivity)
      (htube 0) (hcurv 0)
      (fun Θ' K' dl hX hΘ hper hmem hode =>
        injOn_rearTrack_evCircleData_strip (one_lt_rad 0) Θ' K' dl hX hΘ hper hmem hode)
      (by have := rad_pos 1; positivity) (by have := rad_pos 1; positivity)
      (htube 1) (hcurv 1)
      (fun Θ' K' dl hX hΘ hper hmem hode =>
        injOn_rearTrack_evCircleData_strip (one_lt_rad 1) Θ' K' dl hX hΘ hper hmem hode)
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
      (fun t => by
        have hval : ∀ u : ℝ, ((starRingEnd ℂ) (Vc t u) * Ac t u).im / Pp t ^ 2
            = 2 * Real.pi := by
          intro u
          rw [im_conj_Vc_mul_Ac, mul_div_assoc, div_self (pow_ne_zero 2 (Pp_pos t).ne'),
            mul_one]
        simp only [hval]
        simp)
      (fun t u => by
        have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
        rw [circlePath_nu, Vc]
        field_simp
        rw [Complex.I_sq]
        ring)
      curvOfPath_circlePath
      (fun t σ => rfl) (fun t σ => rfl)
      (fun t σ => (sA_pos t).le) (fun t σ => sA_le t)
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
      hM
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := hrest
  refine ⟨Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp => ?_⟩
  have h := hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp
  simpa [SelectedInverseQuotientSpeed.selInvGaugeConst, circlePath] using h


end SmoothCircleShiftSpeedInstance
