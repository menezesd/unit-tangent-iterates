import Mathlib
import UnitTangentIterates.MovingCircleSmooth
import UnitTangentIterates.RearOwnPathDistFrontOnly

/-!
# The moving circle meets the front-curve form of the path-distance assembly

`RearOwnPathDistFrontOnly.pathDist_le_of_front_curve` takes as data only the
front, its tangent angle and curvature, the selected steering angle, the front
arclength period and the change of variable: every velocity in the estimate is
the corresponding partial derivative, produced rather than assumed.  This file
checks its hypotheses for the family of circles of radius `1/sin A(t)`, whose
rear arclength period passes from `2π` to `2π√3`.

The only thing to see is that the canonical partial derivative `∂_t F` of the
front is the velocity `Ḟ` computed in `MovingCircleFront.lean`, and that the
resulting front normal velocity is the `η_F` used there.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleFrontOnly

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrontOnly
  RearOwnHigherRegularity

/-- The canonical parameter derivative of the front of the moving circle is the
velocity `Ḟ` of `MovingCircleFront.lean`. -/
theorem partialTime_Ff : partialTime Ff = Fdotf := by
  have h1 : ContDiff ℝ (1 : ℕ) (uncurry Ff) :=
    contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out)
  funext t s
  exact (hasDerivAt_partialTime (h1.differentiable (by norm_num)) t s).unique
    (hasDerivAt_Ff_time t s)

/-- The resulting front normal velocity is the one computed there. -/
theorem frontNormalVelocityAt_eq : frontNormalVelocityAt Fdotf Th de = etaFf := by
  funext t s
  exact (etaF_eq t s).symm

/-- **The hypotheses of the front-curve form of the assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistFrontOnly.pathDist_le_of_front_curve` holds for the moving
circle. -/
theorem movingCircle_instance_frontCurve :
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
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_curve
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (EF := E) (P := Pp) (Qf' := fun t => -(2 * Real.pi) * profD t / (sA t) ^ 2)
    (F := Ff) (Θ := Th) (δ := de) (K := Kk) (sf := sff)
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
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
    sff_inv
    (by
      intro t
      rw [partialTime_Ff, frontNormalVelocityAt_eq]
      exact fun s => rfl)
    (by
      intro t u
      rw [partialTime_Ff, frontNormalVelocityAt_eq]
      rfl)
    hasDerivAt_rearPeriod
    (by
      rw [partialTime_Ff, frontNormalVelocityAt_eq]
      exact hEF)
    (by
      intro t ht s
      rw [partialTime_Ff, frontNormalVelocityAt_eq]
      simp [etaFf, MovingCircleProfile.profD_eq_zero_outside ht])
    (fun u => rearData0_apply u)
  refine ⟨E, hE0nn, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCircleFrontOnly
