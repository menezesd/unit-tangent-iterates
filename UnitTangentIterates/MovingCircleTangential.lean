import Mathlib
import UnitTangentIterates.MovingCirclePathDist
import UnitTangentIterates.RearOwnPathDistFrameBounds

/-!
# The tangential component of the motion of the moving circle, and its bounds

For the family of `MovingCircleFront.lean` the tangential component of the
motion of the rears, in the rear arclength, is computed in closed form:

```
  ξ(t, x) = A'(t) · ( x / (sin A cos A) − cos A / sin A ) .
```

It grows linearly in `x` — this is the drift that forces the frame bundle of
`RearOwnFrameDrift.lean`, since over one rear period `Q = 2π cos A / sin A` it
changes by `2π A' / sin²A = −Q'(t)`, exactly the closing relation.  Its two
arclength derivatives are, on the other hand, bounded: the first is
`A'/(sin A cos A)` and the second vanishes.

That makes the *prescribed constants* form of the assembly,
`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds`, applicable to a
family whose rear length moves — `RearOwnPathDistCircleBounds.lean` only checked
it for the resting circle, where both constants are zero.

Main results: `frameTangential_eq`, `partialX_frameTangential`,
`partialX_partialX_frameTangential`, `movingCircle_instance_bounds`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist
open scoped BoundedContinuousFunction

namespace MovingCircleTangential

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrameBounds

theorem expI_eq (y : ℝ) :
    Complex.exp (Complex.I * (y : ℂ)) = (Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-! ### The tangential component in closed form -/

/-- **The tangential component of the motion of the selected rears.**  It grows
linearly in the rear arclength: this is the drift of a family of closed curves
whose length moves. -/
theorem frameTangential_eq (t x : ℝ) :
    frameTangential Ydotf (rearOwnAngle Th de sff) t x
      = profD t * (x / (sA t * cA t) - cA t / sA t) := by
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
  rw [frameTangential, show rearOwnAngle Th de sff t x = psi from rfl, hkey]
  simp only [expI_eq, hcos, hsin, hde, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [Thdot, ww, sfft, hsdef, sff]
  field_simp
  linear_combination (profD t * sA t * x) * hpy

theorem contDiff_frameTangential :
    ContDiff ℝ (⊤ : ℕ∞) (uncurry (frameTangential Ydotf (rearOwnAngle Th de sff))) := by
  have heq : uncurry (frameTangential Ydotf (rearOwnAngle Th de sff))
      = fun p : ℝ × ℝ => profD p.1 * (p.2 / (sA p.1 * cA p.1) - cA p.1 / sA p.1) := by
    funext p
    exact frameTangential_eq p.1 p.2
  rw [heq]
  fun_prop (disch := intros; simp [sA_ne, cA_ne])

/-- The first arclength derivative of the tangential component. -/
theorem partialX_frameTangential (t x : ℝ) :
    partialX (frameTangential Ydotf (rearOwnAngle Th de sff)) t x
      = profD t / (sA t * cA t) := by
  have hne : sA t * cA t ≠ 0 := mul_ne_zero (sA_ne t) (cA_ne t)
  have h1 : HasDerivAt (frameTangential Ydotf (rearOwnAngle Th de sff) t)
      (partialX (frameTangential Ydotf (rearOwnAngle Th de sff)) t x) x :=
    hasDerivAt_partialX (contDiff_frameTangential.of_le (by exact ENat.LEInfty.out)) t x
  have h2 : HasDerivAt (frameTangential Ydotf (rearOwnAngle Th de sff) t)
      (profD t / (sA t * cA t)) x := by
    have hfun : frameTangential Ydotf (rearOwnAngle Th de sff) t
        = fun y => profD t * (y / (sA t * cA t) - cA t / sA t) := funext (frameTangential_eq t)
    rw [hfun]
    have := (((hasDerivAt_id x).div_const (sA t * cA t)).sub_const (cA t / sA t)).const_mul
      (profD t)
    refine this.congr_deriv ?_
    field_simp
  exact h1.unique h2

/-- The second arclength derivative of the tangential component vanishes. -/
theorem partialX_partialX_frameTangential (t x : ℝ) :
    partialX (partialX (frameTangential Ydotf (rearOwnAngle Th de sff))) t x = 0 := by
  have hne : ∀ r : ℝ, sA r * cA r ≠ 0 := fun r => mul_ne_zero (sA_ne r) (cA_ne r)
  have heq : partialX (frameTangential Ydotf (rearOwnAngle Th de sff))
      = fun t _ => profD t / (sA t * cA t) := by
    funext t y
    exact partialX_frameTangential t y
  have hC : ContDiff ℝ 1 (uncurry (partialX (frameTangential Ydotf (rearOwnAngle Th de sff)))) := by
    rw [heq]
    show ContDiff ℝ 1 fun p : ℝ × ℝ => profD p.1 / (sA p.1 * cA p.1)
    fun_prop (disch := intros; simp [sA_ne, cA_ne])
  have h1 := hasDerivAt_partialX hC t x
  have h2 : HasDerivAt (partialX (frameTangential Ydotf (rearOwnAngle Th de sff)) t) 0 x := by
    rw [heq]
    exact hasDerivAt_const x _
  exact h1.unique h2

/-! ### The bounds -/

theorem exists_profD_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |profD t| ≤ M := by
  have hcont : ContinuousOn (fun t => |profD t|) (Icc (0 : ℝ) 1) :=
    (contDiff_profD.continuous.abs).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (by
    exact ⟨0, by norm_num⟩) hcont
  refine ⟨|profD t0|, abs_nonneg _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact hmax ht
  · have h0 : profD t = 0 := by
      refine profD_eq_zero_outside (fun hmem => ht ⟨hmem.1.le, hmem.2.le⟩)
    rw [h0, abs_zero]
    exact abs_nonneg _

theorem sA_mul_cA_ge (t : ℝ) : 1 / 4 ≤ sA t * cA t := by
  have h1 : (1 : ℝ) / 2 ≤ sA t := sA_ge t
  have h2 : (1 : ℝ) / 2 ≤ cA t := by
    have hcos : Real.cos (Real.pi / 4) ≤ cA t := by
      refine Real.cos_le_cos_of_nonneg_of_le_pi (prof_pos t).le (by
        have := Real.pi_pos; linarith) (prof_le t)
    rw [Real.cos_pi_div_four] at hcos
    have : (1 : ℝ) / 2 ≤ Real.sqrt 2 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  nlinarith

/-- **The two gauge constants of the moving circle are explicit.**  Its
tangential component has first arclength derivative bounded by `4M`, `M` a bound
for the derivative of the steering profile, and second arclength derivative
zero. -/
theorem exists_tangential_bounds :
    ∃ rL : ℝ, 0 ≤ rL ∧
      (∀ t x, |partialX (frameTangential Ydotf (rearOwnAngle Th de sff)) t x| ≤ rL) ∧
      ∀ t x, |partialX (partialX (frameTangential Ydotf (rearOwnAngle Th de sff))) t x| ≤ 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_profD_bound
  refine ⟨4 * M, by linarith, fun t x => ?_, fun t x => ?_⟩
  · rw [partialX_frameTangential, abs_div, abs_of_pos (by
      have := sA_mul_cA_ge t; linarith : (0:ℝ) < sA t * cA t)]
    rw [div_le_iff₀ (by have := sA_mul_cA_ge t; linarith : (0:ℝ) < sA t * cA t)]
    have h1 : |profD t| ≤ M := hM t
    have h2 : 1 / 4 ≤ sA t * cA t := sA_mul_cA_ge t
    nlinarith [abs_nonneg (profD t)]
  · rw [partialX_partialX_frameTangential, abs_zero]

/-! ### The assembly with prescribed constants -/

/-- **The hypotheses of the prescribed-constants assembly are met by a family
whose rear length moves.**  Every hypothesis of
`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds` holds for the
moving circle, with the two constants `rL = 4M` and `rB = 0` of
`exists_tangential_bounds`, and the rear arclength period passing from `2π` to
`2π√3`. -/
theorem movingCircle_instance_bounds :
    ∃ rL : ℝ, 0 ≤ rL ∧ ∃ Phi : ℝ → ℝ → ℝ,
      rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
      rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
      (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
      (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
        pathDist rearData0 q' ≤
          gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4)) rL 0 1
            (2 * Real.pi) * cost movingPath := by
  have hpi := Real.pi_pos
  obtain ⟨rL, hrL0, hrL, hrB⟩ := exists_tangential_bounds
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_frame_bounds
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (rL := rL) (rB := 0)
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
    hrL hrB
    (fun t ht => frameNormal_rest ht)
    (fun u => rearData0_apply u)
  refine ⟨rL, hrL0, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCircleTangential
