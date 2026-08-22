import Mathlib
import UnitTangentIterates.MovingCircleTangential
import UnitTangentIterates.RearOwnPathDistGeometric

/-!
# The moving circle meets the geometric form of the path-distance assembly

`RearOwnPathDistGeometric.pathDist_le_of_front_geometric` replaces the two
prescribed gauge constants of the path-distance assembly by two *geometric* sup
bounds: `E₀` for the normal velocity of the selected rears and `E_F` for the
normal velocity of the fronts.  This file checks that its hypotheses can be met
by a family whose rear length genuinely moves — the circles of radius
`1/sin A(t)` of `MovingCircleFront.lean`.

The rear normal velocity is computed in closed form here: it is
`η = A'(t)/sin²A(t)`, constant in the arclength, exactly the rate at which the
radius `cot A(t)` of the selected rear changes.  Together with the front normal
velocity `η_F = cos A · A'/sin²A` both bounds are `4M`, `M` a bound for `A'`.

Main results: `frameNormal_eq`, `movingCircle_instance_geometric`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential
open scoped BoundedContinuousFunction

namespace MovingCircleGeometric

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistGeometric

/-! ### The normal velocity of the selected rears in closed form -/

/-- **The normal velocity of the selected rears of the moving circle.**  The
selected rear is the circle of radius `cot A(t)`, so it moves normally at the
rate `A'(t)/sin²A(t)`, the same at every point. -/
theorem frameNormal_eq (t x : ℝ) :
    frameNormal Ydotf (rearOwnAngle Th de sff) t x = profD t / (sA t) ^ 2 := by
  have hs : sA t ≠ 0 := sA_ne t
  have hc : cA t ≠ 0 := cA_ne t
  have hpy : (sA t) ^ 2 + (cA t) ^ 2 = 1 := by simp [sA, cA, Real.sin_sq_add_cos_sq]
  set s : ℝ := sff t x with hsdef
  set th : ℝ := Th t s with hthdef
  set psi : ℝ := rearAngle (Th t) (de t) s with hpsidef
  have hpsi : psi = th - prof t := rfl
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
      = Complex.exp (Complex.I * ((-psi : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [Complex.conj_I]
  have hE2C : Complex.exp (Complex.I * (psi : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 := by
    rw [hconj, ← Complex.exp_add]
    push_cast
    rw [show Complex.I * (psi : ℂ) + Complex.I * -(psi : ℂ) = 0 by ring, Complex.exp_zero]
  have hE1C : Complex.exp (Complex.I * (th : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
      = Complex.exp (Complex.I * ((prof t : ℝ) : ℂ)) := by
    rw [hconj, ← Complex.exp_add]
    congr 1
    rw [hpsi]
    push_cast
    ring
  have hkey : Ydotf t x * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
      = -Complex.I * ((cA t * profD t : ℝ) : ℂ)
          * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((prof t : ℝ) : ℂ))
        + (-Complex.I * ((Thdot t s - ww t s : ℝ) : ℂ)
          + ((sfft t x * Real.cos (de t s) : ℝ) : ℂ)) := by
    simp only [Ydotf, trackVelocity, Fdotf, Complex.real_smul, ← hsdef, ← hthdef, ← hpsidef]
    linear_combination (norm := (push_cast; ring1)) (-Complex.I * ((cA t * profD t : ℝ) : ℂ)
        * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))) * hE1C
      + (-Complex.I * ((Thdot t s : ℝ) : ℂ) + Complex.I * ((ww t s : ℝ) : ℂ)
        + ((sfft t x : ℝ) : ℂ) * ((Real.cos (de t s) : ℝ) : ℂ)) * hE2C
  have hcos : Real.cos (prof t) = cA t := rfl
  have hsin : Real.sin (prof t) = sA t := rfl
  have hde : Real.cos (de t s) = cA t := rfl
  rw [frameNormal, show rearOwnAngle Th de sff t x = psi from rfl, hkey]
  simp only [expI_eq, hcos, hsin, hde, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [Thdot, ww, hsdef, sff]
  field_simp
  linear_combination (cA t * profD t) * hpy

/-! ### The two geometric bounds -/

/-- **The two geometric constants of the moving circle are explicit.**  Both the
rear and the front normal velocities are bounded by `4M`, `M` a bound for the
derivative of the steering profile. -/
theorem exists_normal_bounds :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ t x, |frameNormal Ydotf (rearOwnAngle Th de sff) t x| ≤ E) ∧
      ∀ t s, |etaFf t s| ≤ E := by
  obtain ⟨M, hM0, hM⟩ := exists_profD_bound
  have hsq : ∀ t, (1 : ℝ) / 4 ≤ (sA t) ^ 2 := by
    intro t
    have := sA_ge t
    nlinarith [sA_pos t]
  have hcle : ∀ t, cA t ≤ 1 := fun t => Real.cos_le_one (prof t)
  refine ⟨4 * M, by linarith, fun t x => ?_, fun t s => ?_⟩
  · rw [frameNormal_eq, abs_div, abs_of_pos (by nlinarith [hsq t] : (0 : ℝ) < (sA t) ^ 2),
      div_le_iff₀ (by nlinarith [hsq t] : (0 : ℝ) < (sA t) ^ 2)]
    nlinarith [hM t, hsq t, abs_nonneg (profD t)]
  · show |cA t * profD t / (sA t) ^ 2| ≤ 4 * M
    rw [abs_div, abs_of_pos (by nlinarith [hsq t] : (0 : ℝ) < (sA t) ^ 2),
      div_le_iff₀ (by nlinarith [hsq t] : (0 : ℝ) < (sA t) ^ 2), abs_mul,
      abs_of_pos (cA_pos t)]
    nlinarith [hM t, hsq t, hcle t, abs_nonneg (profD t), cA_pos t]

/-! ### The assembly with the geometric constants -/

/-- **The hypotheses of the geometric form of the assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistGeometric.pathDist_le_of_front_geometric` holds for the moving
circle, with `E₀ = E_F = 4M` of `exists_normal_bounds`, and the rear arclength
period passing from `2π` to `2π√3`. -/
theorem movingCircle_instance_geometric :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Phi : ℝ → ℝ → ℝ,
      rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
      rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
      (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
      (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
        pathDist rearData0 q' ≤
          gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4))
            (E * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)))
            ((E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) + E)
                * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
              + E * (2 * Real.sin (Real.pi / 4)
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
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_geometric
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (E0 := E) (EF := E)
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
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
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
    (contDiff_uncurry_Ydot.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_ang.of_le (by exact ENat.LEInfty.out))
    hE0 hEF
    (fun t ht => frameNormal_rest ht)
    (fun u => rearData0_apply u)
  refine ⟨E, hE0nn, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

/-! ### The assembly with the geometric constants -/

/-- **The hypotheses of the geometric form of the assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistGeometric.pathDist_le_of_front_normalVelocity` holds for the moving
circle, with `E₀ = E_F = 4M` of `exists_normal_bounds`, and the rear arclength
period passing from `2π` to `2π√3`. -/
theorem movingCircle_instance_frontOnly :
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
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_normalVelocity
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
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
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
    (contDiff_uncurry_Ydot.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_ang.of_le (by exact ENat.LEInfty.out))
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

end MovingCircleGeometric
