import Mathlib
import UnitTangentIterates.MovingCircleNormalized
import UnitTangentIterates.RearOwnPathDistSteering

/-!
# The moving circle meets the assembly with the steering angle produced

`RearOwnPathDistSteering.exists_steering_pathDist_le_of_front` is the
path-distance bound for the selected rears of a normal path of fronts in which
the selected steering angle, its arclength form and the change of variable from
the rear to the front arclength are all **produced** from the front curvature.

This file checks that its hypotheses are consistent, and consistent with a
genuinely moving front period: the family of circles of radius `1/sin A(t)` of
`MovingCircleNormalized.lean`, whose normalized curvature is `K̂(t, σ) = sin A(t)`
and whose front period `P(t) = 2π/sin A(t)` moves, satisfies every one of them.

Main result: `movingCircle_steering_instance`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleSteering

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  MovingCircleFrontOnly MovingCircleCurvature MovingCircleSlices SecondOrderBounds
  MovingCircleNormalized RearOwnPathDistSteering

/-- **The hypotheses of the assembly with the steering angle produced are met by
a family whose period moves.**  For the circles of radius `1/sin A(t)` the
selected steering angle, its arclength form and the change of variable are
produced from the curvature alone, and the resulting rear curves are at path
pseudodistance at most a constant times the cost of the front path. -/
theorem movingCircle_steering_instance :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (Real.sin (Real.pi / 4)))) ∧
      (∀ t σ, HasDerivAt (dn t) (Pp t * (Kk t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / Pp t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∀ p' : Data, (∀ u, p'.1 u = rearOwn Ff Th δ sf 0 (rearArclength (δ 0) (Pp 0) * u)) →
        ∃ (C : ℝ) (Phi : ℝ → ℝ → ℝ), (∀ u, Phi 0 u = rearArclength (δ 0) (Pp 0) * u) ∧
          ∀ q' : Data,
            (∀ u, q'.1 u = rearOwn Ff Th δ sf movingPath.T (Phi movingPath.T u)) →
            pathDist p' q' ≤ C * cost movingPath := by
  have hpi := Real.pi_pos
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CKb, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    exists_steering_pathDist_le_of_front
      (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (Pd := Ppd) (F := Ff) (Θ := Th)
      (Kn := Kk) (Kdn := fun t _ => sAd t)
      (Md := Md) (MP := 8 * Real.pi * Md) (Klip := Md) (Plip := 8 * Real.pi * Md)
      (CK := CKb) (CP := 16 * Real.pi * (CKb + 2 * Md ^ 2))
      movingPath
      (by positivity) hsin4pos hsin4
      (fun t => by
        rw [Pp, le_div_iff₀ (sA_pos t)]
        nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
      (fun t => by
        rw [Pp, div_le_iff₀ (sA_pos t)]
        nlinarith [sA_ge t])
      (fun t s => rfl) (fun t s => rfl)
      (fun t σ => (sA_pos t).le) (fun t σ => sA_le t)
      (fun t σ => hMd t) (abs_Ppd_le hMd)
      (fun a b σ => by
        simpa [Kk] using abs_sub_le_of_deriv_bound hasDerivAt_sAd hMd a b)
      (fun a b => abs_sub_le_of_deriv_bound hasDerivAt_Pp (abs_Ppd_le hMd) a b)
      (fun a b σ => by
        simpa [Kk] using abs_taylor_quadratic hasDerivAt_sAd hasDerivAt_sAdd hCK a b)
      (fun a b => abs_taylor_quadratic hasDerivAt_Pp hasDerivAt_Ppd (abs_Ppdd_le hMd hCK) a b)
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
      hasDerivAt_Ff_space hasDerivAt_Th_space
      Ff_periodic Th_periodic
      (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
      (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
      movingPath_X_eq movingPath_nu_eq
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  intro p' hstart
  obtain ⟨EF, -, -, Phi, hPhi0, -, hPhi⟩ := hrest p' hstart
  exact ⟨_, Phi, hPhi0, fun q' hq' => hPhi q' hq'⟩

end MovingCircleSteering
