import Mathlib
import UnitTangentIterates.MovingCircleCurvature
import UnitTangentIterates.RearOwnPathDistIntrinsic
import UnitTangentIterates.RearOwnPathDistSlices

/-!
# The moving circle meets the sliced form of the path-distance assembly

`RearOwnPathDistSlices.pathDist_le_of_front_slices` is the path-distance bound
for the selected rears in which the only hypotheses relating the normal path to
the family of fronts are the geometric identifications
`X(t,u) = F(t, P(t) u)` and `ν(t,u) = i e^{iΘ(t, P(t) u)}`; the link between the
normal speed of the path and the front normal velocity, the vanishing of that
velocity outside the time window, its periodicity, its sup bound and the
derivative of the rear arclength period are all derived.

This file checks that the family of circles of radius `1 / sin A(t)` — whose
rear arclength period passes from `2π` to `2π√3` — satisfies its hypotheses, so
that form is not vacuous.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleSlices

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrontOnly
  RearOwnPathDistIntrinsic RearOwnPathDistSlices RearOwnHigherRegularity MovingCircleFrontOnly
  MovingCircleCurvature SecondOrderBounds

/-- The front of the moving circle, read in the normalized parameter, has
tangent angle `2π u`. -/
theorem Th_normalized (t u : ℝ) : Th t (Pp t * u) = 2 * Real.pi * u := by
  rw [Th, Pp]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (sA_ne t), mul_one]

/-- The moving marked curve of the path *is* the family of fronts read in the
normalized parameter. -/
theorem movingPath_X_eq (t u : ℝ) : movingPath.X t u = Ff t (Pp t * u) := by
  have hX : movingPath.X t u = -Complex.I * ((1 / sA t : ℝ) : ℂ) * normExp u := rfl
  rw [hX, Ff, Th_normalized, normExp_eq, mul_comm ((2 * Real.pi * u : ℝ) : ℂ) Complex.I]

/-- And its unit normal is the standard one of the front. -/
theorem movingPath_nu_eq (t u : ℝ) :
    movingPath.nu t u = Complex.I * Complex.exp (Complex.I * ((Th t (Pp t * u) : ℝ) : ℂ)) := by
  have hnu : movingPath.nu t u = Complex.I * normExp u := rfl
  rw [hnu, Th_normalized, normExp_eq, mul_comm ((2 * Real.pi * u : ℝ) : ℂ) Complex.I]

/-- **The hypotheses of the sliced form of the assembly are met by a family
whose rear length moves.**  The sup bound `E` of the front normal velocity is
produced by the statement, together with the path-distance bound it enters. -/
theorem movingCircle_instance_slices :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ t s, |frontNormalVelocityAt (partialTime Ff) Th de t s| ≤ E) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
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
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CK, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  obtain ⟨E, hE0, hEF, Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_slices
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (P := Pp) (F := Ff) (Θ := Th) (δ := de) (K := Kk) (Kd := fun t _ => sAd t) (sf := sff)
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
      have hden : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA :=
        contDiff_sA.of_le (by exact ENat.LEInfty.out)
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
    movingPath_X_eq movingPath_nu_eq
    (fun u => rearData0_apply u)
  refine ⟨E, hE0, hEF, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCircleSlices
