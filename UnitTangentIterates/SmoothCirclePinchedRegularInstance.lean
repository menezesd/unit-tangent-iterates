import Mathlib
import UnitTangentIterates.TurningNumberSelInvRegular
import UnitTangentIterates.MarkedSelInvRegular
import UnitTangentIterates.TurningNumberSelInv
import UnitTangentIterates.SmoothCircleShiftEmbeddedInstance

/-!
# The consolidated shift and marked bounds are not vacuous

`TurningNumberSelInvRegular.exists_pinched_pathDistShift_selInv_le_regular` and
`MarkedSelInvRegular.exists_pinched_pathDist_selInv_le_regular` state the bounds
for the marked selected inverses of the two ends of a normal path with neither
the global topological hypotheses nor the quantitative time bounds of the front
data assumed.  What is left are the tube data of the two ends, the curvature
pinching with the length thresholds, the geometry of the path and the `C⁴`
regularity of its position, velocity and acceleration.

This file checks that this hypothesis block is consistent, on the witness used
for the previous forms of the bound: the smooth dilation of a circle of
`SmoothCircleShiftInstance.lean`, the family of circles of radius `1 / sin A(t)`
running from the marked circle of radius `√2` to that of radius `2`.

Main results: `circlePath_pinched_regular_instance` (modulo the marking) and
`circlePath_pinched_marked_instance` (the marked pseudodistance).
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SmoothCirclePinchedRegularInstance

open MovingCircleProfile MovingCircleCurvature MovingCircle MovingCircleNormalized
  FrontFromPath SelectedInverseCircle SelectedInverseTubeCircle SmoothCircleShiftInstance
  SmoothCircleShiftEmbeddedInstance TurningNumberSelInv

/-! ### The data of the dilating circle -/

/-- The curvature ceiling of the instance, `κ̂ = sin(π/4)`, is below one. -/
theorem sin_pi_div_four_lt_one : Real.sin (Real.pi / 4) < 1 := by
  rw [Real.sin_pi_div_four]
  nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- The curvature ceiling of the instance is nonnegative. -/
theorem sin_pi_div_four_nonneg : 0 ≤ Real.sin (Real.pi / 4) := by
  rw [Real.sin_pi_div_four]; positivity

/-- Every slice of the dilating circle is a member of the tube. -/
theorem circle_tube (t : ℝ) : IsTubeMember (2 * Real.pi * rad t) (1 / rad t) (4 * rad t)
    (circleData (rad t)) := circleData_mem_tube (rad_pos t)

/-- The curvature of every slice is at most `sin(π/4)`. -/
theorem circle_curv (t u : ℝ) :
    ((starRingEnd ℂ) ((circleData (rad t)).2.1 u) * (circleData (rad t)).2.2 u).im
      ≤ Real.sin (Real.pi / 4) * ‖(circleData (rad t)).2.1 u‖ ^ 3 := by
  have h := SelectedInverseTubeCircle.circleData_curvature_le (rad_pos t) u
  have hle : 1 / rad t ≤ Real.sin (Real.pi / 4) := by
    rw [rad, one_div_one_div]
    exact sA_le t
  have hnn : (0 : ℝ) ≤ ‖(circleData (rad t)).2.1 u‖ ^ 3 := by positivity
  nlinarith

/-- The length threshold `κ̂ · L < 4π` holds for every slice. -/
theorem circle_short_perim (t : ℝ) :
    Real.sin (Real.pi / 4) * perim (circleData (rad t)) < 4 * Real.pi := by
  rw [perim_circleData (rad_pos t)]
  exact circle_short t

/-- The period of the dilating circle is at least `2π`. -/
theorem circle_Pp_lower (t : ℝ) : 2 * Real.pi ≤ Pp t := by
  have hpi := Real.pi_pos
  rw [Pp, le_div_iff₀ (sA_pos t)]
  nlinarith [sA_le t, sin_pi_div_four_lt_one, Real.sin_le_one (prof t), sA_pos t]

/-- The period of the dilating circle is at most `4π`. -/
theorem circle_Pp_upper (t : ℝ) : Pp t ≤ 4 * Real.pi := by
  have hpi := Real.pi_pos
  rw [Pp, div_le_iff₀ (sA_pos t)]
  nlinarith [sA_ge t]

/-- The unit normal of the path is the rotated normalized velocity. -/
theorem circle_nu (t u : ℝ) : circlePath.nu t u = Complex.I * (Vc t u / (Pp t : ℂ)) := by
  have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
  rw [circlePath_nu, Vc]
  field_simp
  rw [Complex.I_sq]
  ring

/-- The position of the dilating circle is jointly smooth. -/
theorem contDiff_uncurry_X {n : ℕ} : ContDiff ℝ (n : ℕ) (uncurry circlePath.X) := by
  have hfun : uncurry circlePath.X
      = fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ) * normExp p.2 := by
    funext p; rw [uncurry, circlePath_X]
  rw [hfun]
  exact (contDiff_ofReal.comp (contDiff_rad.comp contDiff_fst)).mul
    (contDiff_normExp.comp contDiff_snd)

/-- The velocity of the dilating circle is jointly smooth. -/
theorem contDiff_uncurry_Vc {n : ℕ} : ContDiff ℝ (n : ℕ) (uncurry Vc) := by
  have hfun : uncurry Vc
      = fun p : ℝ × ℝ => ((Pp p.1 : ℝ) : ℂ) * Complex.I * normExp p.2 := by
    funext p; rw [uncurry, Vc]
  rw [hfun]
  exact ((contDiff_ofReal.comp ((contDiff_Pp n).comp contDiff_fst)).mul
    contDiff_const).mul (contDiff_normExp.comp contDiff_snd)

/-- The acceleration of the dilating circle is jointly smooth. -/
theorem contDiff_uncurry_Ac {n : ℕ} : ContDiff ℝ (n : ℕ) (uncurry Ac) := by
  have hfun : uncurry Ac
      = fun p : ℝ × ℝ => -((2 * Real.pi * Pp p.1 : ℝ) : ℂ) * normExp p.2 := by
    funext p; rw [uncurry, Ac]
  rw [hfun]
  exact ((contDiff_ofReal.comp
    (contDiff_const.mul ((contDiff_Pp n).comp contDiff_fst))).neg).mul
    (contDiff_normExp.comp contDiff_snd)

/-- The normalized curvature of the dilating circle is jointly smooth. -/
theorem contDiff_uncurry_Kk {n : ℕ} : ContDiff ℝ (n : ℕ) (uncurry Kk) := by
  have h : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) sA :=
    contDiff_sA.of_le (by exact ENat.LEInfty.out)
  simpa [Kk, uncurry] using h.comp contDiff_fst

/-- The tangent at the marked point of every slice is vertical, hence in the
slit plane. -/
theorem circle_slit (t : ℝ) : Vc t 0 ∈ Complex.slitPlane := by
  have hPne : Pp t ≠ 0 := (Pp_pos t).ne'
  have hval : Vc t 0 = ((Pp t : ℝ) : ℂ) * Complex.I := by
    rw [Vc]
    have h0 : normExp 0 = 1 := by simp [normExp]
    rw [h0, mul_one]
  refine Or.inr ?_
  rw [hval]
  simpa using hPne

/-! ### The two instances -/

/-- **The hypotheses of the consolidated shift bound are consistent.**  They
hold for the smooth dilation of a circle: its slices are circles of radius
`1/sin A(t) ∈ [√2, 2]`, so their curvature is pinched by `1/2 ≤ K̂ ≤ sin(π/4)`
and the length threshold `sin(π/4)·L < 4π` holds at every time, while the
position, the velocity and the acceleration of the path are smooth and the
tangent at the marked point of every slice is vertical. -/
theorem circlePath_pinched_regular_instance :
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
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    TurningNumberSelInvRegular.exists_pinched_pathDistShift_selInv_le_regular
      (M := M) (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (V := Vc) (A := Ac) (Kn := Kk)
      (c := 2 * Real.pi * rad 0) (kmin := 1 / rad 0) (dlt := 4 * rad 0)
      (cq := 2 * Real.pi * rad 1) (kminq := 1 / rad 1) (dltq := 4 * rad 1)
      (kminK := 1 / 2)
      circlePath
      (by have := rad_pos 0; positivity) (by have := rad_pos 0; positivity)
      (circle_tube 0) (circle_curv 0) (circle_short_perim 0)
      (by have := rad_pos 1; positivity) (by have := rad_pos 1; positivity)
      (circle_tube 1) (circle_curv 1) (circle_short_perim 1)
      (by positivity) sin_pi_div_four_nonneg sin_pi_div_four_lt_one
      circle_Pp_lower circle_Pp_upper
      hasDerivAt_Vc hasDerivAt_Ac
      (fun t => (continuous_const.mul continuous_normExp))
      norm_Vc
      (fun t u => by simp [periodic_normExp u])
      (fun t u => by simp [Vc, periodic_normExp u])
      (fun t u => by simp [Ac, periodic_normExp u])
      circle_nu
      curvOfPath_circlePath
      (fun t σ => rfl)
      (by norm_num) (fun t σ => sA_ge t) (fun t σ => sA_le t)
      (fun t => by
        rw [Pp_eq_two_pi_mul_rad t]
        exact circle_short t)
      (contDiff_Pp 4) contDiff_uncurry_Kk contDiff_uncurry_X contDiff_uncurry_Vc
      contDiff_uncurry_Ac circle_slit hM
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := hrest
  refine ⟨Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp => ?_⟩
  have h := hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp
  simpa [SelectedInverseQuotientSpeed.selInvGaugeConst, circlePath] using h

/-- **The hypotheses of the consolidated marked bound are consistent.**  The
same witness satisfies the hypothesis block of
`MarkedSelInvRegular.exists_pinched_pathDist_selInv_le_regular`, whose
conclusion is a bound for the marked path pseudodistance under the extra
geometric condition that the marked point of the front is at rest. -/
theorem circlePath_pinched_marked_instance :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (Real.sin (Real.pi / 4)))) ∧
      (∀ t σ, HasDerivAt (dn t) (Pp t * (Kk t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / Pp t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ C : ℝ, ∃ Phi : ℝ → ℝ → ℝ,
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
          (∀ t, circlePath.eta t 0 = 0) →
          pathDist
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 0)))
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 1)))
            ≤ C * cost circlePath := by
  have hpi := Real.pi_pos
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    MarkedSelInvRegular.exists_pinched_pathDist_selInv_le_regular
      (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (V := Vc) (A := Ac) (Kn := Kk)
      (c := 2 * Real.pi * rad 0) (kmin := 1 / rad 0) (dlt := 4 * rad 0)
      (cq := 2 * Real.pi * rad 1) (kminq := 1 / rad 1) (dltq := 4 * rad 1)
      (kminK := 1 / 2)
      circlePath
      (by have := rad_pos 0; positivity) (by have := rad_pos 0; positivity)
      (circle_tube 0) (circle_curv 0) (circle_short_perim 0)
      (by have := rad_pos 1; positivity) (by have := rad_pos 1; positivity)
      (circle_tube 1) (circle_curv 1) (circle_short_perim 1)
      (by positivity) sin_pi_div_four_nonneg sin_pi_div_four_lt_one
      circle_Pp_lower circle_Pp_upper
      hasDerivAt_Vc hasDerivAt_Ac
      (fun t => (continuous_const.mul continuous_normExp))
      norm_Vc
      (fun t u => by simp [periodic_normExp u])
      (fun t u => by simp [Vc, periodic_normExp u])
      (fun t u => by simp [Ac, periodic_normExp u])
      circle_nu
      curvOfPath_circlePath
      (fun t σ => rfl)
      (by norm_num) (fun t σ => sA_ge t) (fun t σ => sA_le t)
      (fun t => by
        rw [Pp_eq_two_pi_mul_rad t]
        exact circle_short t)
      (contDiff_Pp 4) contDiff_uncurry_Kk contDiff_uncurry_X contDiff_uncurry_Vc
      contDiff_uncurry_Ac circle_slit
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨EF, -, -, Phi, hPhi0, hPhi⟩ := hrest
  exact ⟨_, Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp hrest0 =>
    hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp hrest0⟩

end SmoothCirclePinchedRegularInstance
