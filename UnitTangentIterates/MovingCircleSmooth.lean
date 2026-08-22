import Mathlib
import UnitTangentIterates.MovingCircleGeometric
import UnitTangentIterates.RearOwnPathDistSmooth

/-!
# The moving circle meets the fully reduced form of the path-distance assembly

`RearOwnPathDistSmooth.pathDist_le_of_front_regularity` asks only for the front
data: two-sided bounds for the front period, the selected strip, a sup bound for
the front normal velocity, and joint `C⁴` regularity of the front, of its
tangent angle and of the selected steering angle.  This file checks that all of
that holds for the family of circles of radius `1/sin A(t)`, whose front data
are smooth, so that the fully reduced assembly is not vacuous either: the rear
arclength period of that family passes from `2π` to `2π√3`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleSmooth

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth

/-- **The hypotheses of the fully reduced form of the assembly are met by a
family whose rear length moves.**  Every hypothesis of
`RearOwnPathDistSmooth.pathDist_le_of_front_regularity` holds for the moving
circle, with `E_F = 4M` of `exists_normal_bounds`, and the rear arclength period
passing from `2π` to `2π√3`. -/
theorem movingCircle_instance_smooth :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Phi : ℝ → ℝ → ℝ,
      rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
      rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
      (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
      (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
        pathDist rearData0 q' ≤
          gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4))
            (E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
              * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)))
            ((E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
                  + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
                * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
              + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) * (2 * Real.sin (Real.pi / 4)
                / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) ^ 3)) 1
            (2 * Real.pi) * cost movingPath := by
  have hpi := Real.pi_pos
  obtain ⟨E, hE0nn, hE0, hEF⟩ := exists_normal_bounds
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_regularity
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (EF := E)
    (P := Pp) (Qf' := fun t => -(2 * Real.pi) * profD t / (sA t) ^ 2)
    (F := Ff) (Fdot := Fdotf) (Fdots := Fdotsf) (Ydot := Ydotf)
    (Θ := Th) (δ := de) (K := Kk) (etaF := etaFf) (etaFs := fun _ _ => 0)
    (sf := sff) (sft := sfft) (dt := ww) (Θdot := Thdot) (w := ww)
    (Θdots := Thdots) (ws := fun _ _ => 0)
    movingPath rearData0
    (by positivity) hsin4pos hsin4
    (fun t => by
      rw [Pp, le_div_iff₀ (sA_pos t)]
      nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
    (fun t => by
      rw [Pp, div_le_iff₀ (sA_pos t)]
      nlinarith [sA_ge t])
    hasDerivAt_Ff_space hasDerivAt_Th_space hasDerivAt_de_space
    (fun t s => (prof_pos t).le)
    (fun t s => by rw [harcsin]; exact prof_le t)
    de_periodic
    (fun t s => by
      rw [Kk, abs_of_pos (sA_pos t)]
      exact sA_le t)
    (fun t => continuous_const)
    Ff_periodic Th_periodic
    hasDerivAt_de_time
    (by
      show Continuous fun p : ℝ × ℝ => profD p.1
      exact contDiff_profD.continuous.comp continuous_fst)
    etaF_eq
    (fun t s => hasDerivAt_const s (etaFf t 0))
    (fun t => continuous_const)
    (fun t s => rfl)
    (fun t u => rfl)
    sff_inv hasDerivAt_sff_time hasDerivAt_Ff_time hasDerivAt_Th_time hasDerivAt_de_time
    hasDerivAt_Fdot_space hasDerivAt_Thdot_space hasDerivAt_ww_space
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
    (fun t x => rfl)
    hasDerivAt_rearPeriod
    hEF
    (fun t ht => frameNormal_rest ht)
    (fun u => rearData0_apply u)
  refine ⟨E, hE0nn, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

/-- **The hypotheses of the front-only form of the assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistSmooth.pathDist_le_of_front_data` holds for the moving circle:
the front normal velocity `cos A · A'/sin²A` vanishes outside the time window,
so the rest of the selected rears there need not be checked separately. -/
theorem movingCircle_instance_frontData :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Phi : ℝ → ℝ → ℝ,
      rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
      rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
      (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
      (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
        pathDist rearData0 q' ≤
          gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4))
            (E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
              * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)))
            ((E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
                  + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
                * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
              + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) * (2 * Real.sin (Real.pi / 4)
                / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) ^ 3)) 1
            (2 * Real.pi) * cost movingPath := by
  have hpi := Real.pi_pos
  obtain ⟨E, hE0nn, hE0, hEF⟩ := exists_normal_bounds
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_data
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (EF := E)
    (P := Pp) (Qf' := fun t => -(2 * Real.pi) * profD t / (sA t) ^ 2)
    (F := Ff) (Fdot := Fdotf) (Fdots := Fdotsf) (Ydot := Ydotf)
    (Θ := Th) (δ := de) (K := Kk) (etaF := etaFf) (etaFs := fun _ _ => 0)
    (sf := sff) (sft := sfft) (dt := ww) (Θdot := Thdot) (w := ww)
    (Θdots := Thdots) (ws := fun _ _ => 0)
    movingPath rearData0
    (by positivity) hsin4pos hsin4
    (fun t => by
      rw [Pp, le_div_iff₀ (sA_pos t)]
      nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
    (fun t => by
      rw [Pp, div_le_iff₀ (sA_pos t)]
      nlinarith [sA_ge t])
    hasDerivAt_Ff_space hasDerivAt_Th_space hasDerivAt_de_space
    (fun t s => (prof_pos t).le)
    (fun t s => by rw [harcsin]; exact prof_le t)
    de_periodic
    (fun t s => by
      rw [Kk, abs_of_pos (sA_pos t)]
      exact sA_le t)
    (fun t => continuous_const)
    Ff_periodic Th_periodic
    hasDerivAt_de_time
    (by
      show Continuous fun p : ℝ × ℝ => profD p.1
      exact contDiff_profD.continuous.comp continuous_fst)
    etaF_eq
    (fun t s => hasDerivAt_const s (etaFf t 0))
    (fun t => continuous_const)
    (fun t s => rfl)
    (fun t u => rfl)
    sff_inv hasDerivAt_sff_time hasDerivAt_Ff_time hasDerivAt_Th_time hasDerivAt_de_time
    hasDerivAt_Fdot_space hasDerivAt_Thdot_space hasDerivAt_ww_space
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
    (fun t x => rfl)
    hasDerivAt_rearPeriod
    hEF
    (fun t ht s => by
      simp [MovingCircle.etaFf, MovingCircleProfile.profD_eq_zero_outside ht])
    (fun u => rearData0_apply u)
  refine ⟨E, hE0nn, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCircleSmooth
