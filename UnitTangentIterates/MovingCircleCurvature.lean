import Mathlib
import UnitTangentIterates.MovingCircleFrontOnly
import UnitTangentIterates.RearOwnPathDistCurvature
import UnitTangentIterates.SecondOrderBounds

/-!
# The moving circle meets the curvature form of the path-distance assembly

`RearOwnPathDistCurvature.pathDist_le_of_front_curvature` is the path-distance
bound for the selected rears in which the joint `C⁴` regularity of the steering
angle is *derived* from the front curvature.  Its hypotheses on the curvature
are the joint `C³` regularity of the curvature, of its parameter derivative and
of the front period, together with a Lipschitz bound, a first-order Taylor
bound and a sup bound on the parameter derivative.

This file checks them for the family of circles of radius `1 / sin A(t)`, whose
rear arclength period passes from `2π` to `2π√3`: the curvature is `sin A(t)`,
its parameter derivative `cos A(t) · A'(t)` is continuous and vanishes outside
the time window, hence bounded, and the two increment bounds follow from the
global bounds on the first and second derivatives.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleCurvature

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrontOnly
  RearOwnPathDistCurvature RearOwnHigherRegularity MovingCircleFrontOnly
  SecondOrderBounds

/-- The parameter derivative of the curvature of the moving circle. -/
def sAd (t : ℝ) : ℝ := cA t * profD t

/-- Its own derivative. -/
def sAdd : ℝ → ℝ := deriv sAd

@[fun_prop]
theorem contDiff_sAd : ContDiff ℝ (⊤ : ℕ∞) sAd := by
  unfold sAd; fun_prop

@[fun_prop]
theorem contDiff_sAdd : ContDiff ℝ (⊤ : ℕ∞) sAdd := ContDiff.deriv' contDiff_sAd

theorem differentiable_sAd : Differentiable ℝ sAd :=
  contDiff_sAd.differentiable (by simp)

theorem hasDerivAt_sAd (t : ℝ) : HasDerivAt sA (sAd t) t := hasDerivAt_sA t

theorem hasDerivAt_sAdd (t : ℝ) : HasDerivAt sAd (sAdd t) t :=
  (differentiable_sAd t).hasDerivAt

/-- The profile is frozen near any time to the left of the window. -/
theorem profD_eventually_zero_left {t : ℝ} (ht : t < 1 / 4) : profD =ᶠ[nhds t] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds ht] with x hx using profD_of_lt hx

/-- And near any time to the right of it. -/
theorem profD_eventually_zero_right {t : ℝ} (ht : 3 / 4 < t) : profD =ᶠ[nhds t] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds ht] with x hx using profD_of_gt hx

theorem sAd_eq_zero_outside {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : sAd t = 0 := by
  have h : profD t = 0 := by
    refine profD_eq_zero_outside (fun hmem => ht ⟨hmem.1.le, hmem.2.le⟩)
  simp [sAd, h]

theorem sAdd_eq_zero_outside {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : sAdd t = 0 := by
  have hev : sAd =ᶠ[nhds t] fun _ => 0 := by
    rcases lt_or_ge t 0 with h | h
    · filter_upwards [profD_eventually_zero_left (by linarith : t < 1 / 4)] with x hx
      simp [sAd, hx]
    · have h1 : 1 < t := by
        by_contra hc
        exact ht ⟨h, le_of_not_gt hc⟩
      filter_upwards [profD_eventually_zero_right (by linarith : 3 / 4 < t)] with x hx
      simp [sAd, hx]
  rw [sAdd, hev.deriv_eq]
  simp

/-- **The hypotheses of the curvature form of the assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistCurvature.pathDist_le_of_front_curvature` — in particular the
joint `C³` regularity of the curvature, of its parameter derivative and of the
period, and the increment bounds in the path parameter — holds for the moving
circle, and the joint `C⁴` regularity of the steering angle is no longer
assumed. -/
theorem movingCircle_instance_curvature :
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
  -- the global bounds on the first two derivatives of the curvature
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CK, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_curvature
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (EF := E) (P := Pp) (Qf' := fun t => -(2 * Real.pi) * profD t / (sA t) ^ 2)
    (F := Ff) (Θ := Th) (δ := de) (K := Kk) (Kd := fun t _ => sAd t) (sf := sff)
    (Md := Md) (Klip := Md) (CK := CK)
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
    (fun t s => rfl)
    (fun t s => hMd t)
    (fun a b s => by
      simpa [Kk] using abs_sub_le_of_deriv_bound hasDerivAt_sAd hMd a b)
    (fun a b s => by
      simpa [Kk] using abs_taylor_quadratic hasDerivAt_sAd hasDerivAt_sAdd hCK a b)
    hCK0
    (by
      have hden : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
      have : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun t => 2 * Real.pi / sA t) :=
        contDiff_const.div hden (fun t => sA_ne t)
      simpa [Pp] using this)
    (by
      have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
      simpa [Kk, uncurry] using h.comp contDiff_fst)
    (by
      have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sAd :=
        contDiff_sAd.of_le (by exact ENat.LEInfty.out)
      simpa [uncurry] using h.comp contDiff_fst)
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

end MovingCircleCurvature
