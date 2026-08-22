import Mathlib
import UnitTangentIterates.SmoothCircleShiftTaylorInstance
import UnitTangentIterates.SelectedInverseShiftPathRegularity

/-!
# The shift bound with the front data reduced to the path is not vacuous

`SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathRegular`
states the shift bound with the regularity of the front family and of its
tangent angle replaced by that of the position, the velocity and the
acceleration of the path.  This file checks that its hypotheses are consistent,
on the same smooth dilation of a circle used for the previous forms: the family
of circles of radius `1 / sin A(t)`, whose ends are the marked circles of radius
`√2` and `2`.

Main result: `circlePath_shift_instance_pathRegular`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SmoothCirclePathRegularityInstance

open MovingCircleProfile MovingCircleCurvature MovingCircle MovingCircleNormalized
  FrontFromPath SelectedInverseCircle SelectedInverseTubeCircle SmoothCircleShiftInstance

/-- The normalized exponential is smooth. -/
theorem contDiff_normExp {n : ℕ} : ContDiff ℝ (n : ℕ) normExp := by
  have h : normExp = fun u : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (u : ℂ)) := by
    funext u; rw [normExp]; ring_nf
  rw [h]
  exact ((Complex.contDiff_exp (𝕜 := ℂ) (n := (n : ℕ))).restrict_scalars ℝ).comp
    (contDiff_const.mul contDiff_ofReal)

/-- **The hypotheses of the shift bound with the front data reduced to the data
of the path are consistent.**  They hold for the smooth dilation of a circle,
the tangent at the marked point of every slice being the vertical unit vector,
whose argument is the constant `π/2`. -/
theorem circlePath_shift_instance_pathRegular :
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
    SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathRegular
      (M := M) (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (V := Vc) (A := Ac) (Kn := Kk)
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
      (fun t σ => rfl)
      (fun t σ => (sA_pos t).le) (fun t σ => sA_le t)
      (contDiff_Pp 4)
      (by
        have h : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) sA :=
          contDiff_sA.of_le (by exact ENat.LEInfty.out)
        simpa [Kk, uncurry] using h.comp contDiff_fst)
      (by
        have hfun : uncurry circlePath.X
            = fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ) * normExp p.2 := by
          funext p; rw [uncurry, circlePath_X]
        rw [hfun]
        exact (contDiff_ofReal.comp (contDiff_rad.comp contDiff_fst)).mul
          (contDiff_normExp.comp contDiff_snd))
      (by
        have hfun : uncurry Vc
            = fun p : ℝ × ℝ => ((Pp p.1 : ℝ) : ℂ) * Complex.I * normExp p.2 := by
          funext p; rw [uncurry, Vc]
        rw [hfun]
        exact ((contDiff_ofReal.comp ((contDiff_Pp 4).comp contDiff_fst)).mul
          contDiff_const).mul (contDiff_normExp.comp contDiff_snd))
      (by
        have hfun : uncurry Ac
            = fun p : ℝ × ℝ => -((2 * Real.pi * Pp p.1 : ℝ) : ℂ) * normExp p.2 := by
          funext p; rw [uncurry, Ac]
        rw [hfun]
        exact ((contDiff_ofReal.comp
          (contDiff_const.mul ((contDiff_Pp 4).comp contDiff_fst))).neg).mul
          (contDiff_normExp.comp contDiff_snd))
      (by
        have htan : ∀ t : ℝ, (tangentOfPath Vc Pp t 0).arg = Real.pi / 2 := by
          intro t
          have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
          have h : tangentOfPath Vc Pp t 0 = Complex.I := by
            rw [tangentOfPath, Vc, zero_div]
            have h0 : normExp 0 = 1 := by simp [normExp]
            rw [h0]
            field_simp
          rw [h, Complex.arg_I]
        simp only [htan]
        exact contDiff_const)
      hM
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := hrest
  refine ⟨Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp => ?_⟩
  have h := hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp
  simpa [SelectedInverseQuotientSpeed.selInvGaugeConst, circlePath] using h

end SmoothCirclePathRegularityInstance
