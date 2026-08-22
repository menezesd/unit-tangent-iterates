import Mathlib
import UnitTangentIterates.UniformFrameBounds

/-!
# The radius profile of a circle whose length moves

The path-distance assemblies for the selected rears
(`RearOwnPathDistFrameDrift.lean`, `RearOwnPathDistFrameBounds.lean`) no longer
force the arclength period of the rear to be constant along the path.  To show
that this generality is not empty one needs a family of fronts whose rear
*does* change length; the simplest is a circle whose radius moves.

This file provides the time profile of such a family.  It is more convenient to
prescribe the *steering angle* `A(t)` than the radius: a circle of radius
`1 / sin A` has curvature `sin A`, its selected steering angle is the constant
`A`, and its rear is the circle of radius `cos A / sin A`.  The profile

```
  A(t) = π/4 − (π/12) · smoothTransition (2t − ½)
```

decreases smoothly from `π/4` at `t = 0` to `π/6` at `t = 1`, is constant
outside the window `[¼, ¾] ⊆ (0, 1)`, and stays in `[π/6, π/4]`, so the radius
stays in `[√2, 2]` and the curvature in `[½, √2/2]`.

Main definitions: `prof`, `profD`, `sA`, `cA`.
-/

noncomputable section

open Set Function UniformFrameBounds

namespace MovingCircleProfile

/-- The inclusion of the reals in the complexes is smooth; `fun_prop` needs it. -/
@[fun_prop]
theorem contDiff_ofReal {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

/-- The steering-angle profile: it decreases from `π/4` to `π/6`. -/
def prof (t : ℝ) : ℝ := Real.pi / 4 - Real.pi / 12 * Real.smoothTransition (2 * t - 1 / 2)

/-- The time derivative of the profile. -/
def profD : ℝ → ℝ := deriv prof

@[fun_prop]
theorem contDiff_prof : ContDiff ℝ (⊤ : ℕ∞) prof := by
  unfold prof; fun_prop

@[fun_prop]
theorem contDiff_profD : ContDiff ℝ (⊤ : ℕ∞) profD :=
  ContDiff.deriv' contDiff_prof

theorem differentiable_prof : Differentiable ℝ prof := by
  unfold prof; fun_prop

theorem hasDerivAt_prof (t : ℝ) : HasDerivAt prof (profD t) t :=
  (differentiable_prof t).hasDerivAt

theorem prof_zero : prof 0 = Real.pi / 4 := by
  simp [prof]

theorem prof_one : prof 1 = Real.pi / 6 := by
  rw [prof, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2 * 1 - 1 / 2)]
  ring

theorem prof_le (t : ℝ) : prof t ≤ Real.pi / 4 := by
  have h0 := Real.smoothTransition.nonneg (2 * t - 1 / 2)
  have hpi := Real.pi_pos
  rw [prof]; nlinarith

theorem prof_ge (t : ℝ) : Real.pi / 6 ≤ prof t := by
  have h1 := Real.smoothTransition.le_one (2 * t - 1 / 2)
  have hpi := Real.pi_pos
  rw [prof]; nlinarith

theorem prof_pos (t : ℝ) : 0 < prof t :=
  lt_of_lt_of_le (by positivity) (prof_ge t)

theorem prof_lt_pi_div_two (t : ℝ) : prof t < Real.pi / 2 := by
  have := prof_le t
  have := Real.pi_pos
  linarith

/-- The profile is constant to the left of the window. -/
theorem prof_eventuallyEq_left {t : ℝ} (ht : t < 1 / 4) :
    prof =ᶠ[nhds t] fun _ => Real.pi / 4 := by
  filter_upwards [Iio_mem_nhds ht] with x hx
  have h : 2 * x - 1 / 2 ≤ 0 := by
    have : x < 1 / 4 := hx
    linarith
  rw [prof, Real.smoothTransition.zero_of_nonpos h]
  ring

/-- The profile is constant to the right of the window. -/
theorem prof_eventuallyEq_right {t : ℝ} (ht : 3 / 4 < t) :
    prof =ᶠ[nhds t] fun _ => Real.pi / 4 - Real.pi / 12 := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  have hx' : 3 / 4 < x := hx
  rw [prof, Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 2 * x - 1 / 2)]
  ring

theorem profD_of_lt {t : ℝ} (ht : t < 1 / 4) : profD t = 0 := by
  rw [profD, (prof_eventuallyEq_left ht).deriv_eq]
  simp

theorem profD_of_gt {t : ℝ} (ht : 3 / 4 < t) : profD t = 0 := by
  rw [profD, (prof_eventuallyEq_right ht).deriv_eq]
  simp

theorem prof_of_le_zero {t : ℝ} (ht : t ≤ 0) : prof t = Real.pi / 4 := by
  have h : 2 * t - 1 / 2 ≤ 0 := by linarith
  rw [prof, Real.smoothTransition.zero_of_nonpos h]
  ring

theorem prof_of_one_le {t : ℝ} (ht : 1 ≤ t) : prof t = Real.pi / 4 - Real.pi / 12 := by
  rw [prof, Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 2 * t - 1 / 2)]
  ring

/-- Outside the time window the profile does not move. -/
theorem profD_eq_zero_outside {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : profD t = 0 := by
  rcases le_or_gt t 0 with h | h
  · exact profD_of_lt (by linarith)
  · have h1 : 1 ≤ t := by
      by_contra hc
      exact ht ⟨h, lt_of_not_ge hc⟩
    exact profD_of_gt (by linarith)

/-- The profile is frozen outside the time window. -/
theorem prof_clamp (t : ℝ) : prof t = prof (clampT 0 1 t) := by
  rcases le_or_gt t 0 with h | h
  · rw [clampT, min_eq_left (by linarith : t ≤ (1:ℝ)), max_eq_left h]
    rw [prof_of_le_zero h, prof_zero]
  · rcases le_or_gt t 1 with h1 | h1
    · rw [clampT_of_mem ⟨h.le, h1⟩]
    · rw [clampT, min_eq_right h1.le, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      rw [prof_of_one_le h1.le, prof_of_one_le le_rfl]

theorem profD_clamp (t : ℝ) : profD t = profD (clampT 0 1 t) := by
  rcases le_or_gt t 0 with h | h
  · rw [clampT, min_eq_left (by linarith : t ≤ (1:ℝ)), max_eq_left h]
    rw [profD_of_lt (by linarith), profD_of_lt (by norm_num)]
  · rcases le_or_gt t 1 with h1 | h1
    · rw [clampT_of_mem ⟨h.le, h1⟩]
    · rw [clampT, min_eq_right h1.le, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      rw [profD_of_gt (by linarith), profD_of_gt (by norm_num)]

/-! ### The sine and the cosine of the profile -/

/-- The curvature of the front: `sin A`. -/
def sA (t : ℝ) : ℝ := Real.sin (prof t)

/-- The cosine of the steering angle. -/
def cA (t : ℝ) : ℝ := Real.cos (prof t)

@[fun_prop]
theorem contDiff_sA : ContDiff ℝ (⊤ : ℕ∞) sA := Real.contDiff_sin.comp contDiff_prof

@[fun_prop]
theorem contDiff_cA : ContDiff ℝ (⊤ : ℕ∞) cA := Real.contDiff_cos.comp contDiff_prof

theorem sA_pos (t : ℝ) : 0 < sA t :=
  Real.sin_pos_of_pos_of_lt_pi (prof_pos t) (by
    have := prof_lt_pi_div_two t; have := Real.pi_pos; linarith)

theorem cA_pos (t : ℝ) : 0 < cA t :=
  Real.cos_pos_of_mem_Ioo ⟨by have := prof_pos t; have := Real.pi_pos; linarith,
    prof_lt_pi_div_two t⟩

theorem sA_ne (t : ℝ) : sA t ≠ 0 := (sA_pos t).ne'

theorem cA_ne (t : ℝ) : cA t ≠ 0 := (cA_pos t).ne'

theorem sA_le (t : ℝ) : sA t ≤ Real.sin (Real.pi / 4) := by
  refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ (prof_le t)
  · have := prof_pos t; have := Real.pi_pos; linarith
  · have := Real.pi_pos; linarith

theorem sA_ge (t : ℝ) : 1 / 2 ≤ sA t := by
  have h : Real.sin (Real.pi / 6) ≤ sA t := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ (prof_lt_pi_div_two t).le (prof_ge t)
    · have := Real.pi_pos; linarith
  rwa [Real.sin_pi_div_six] at h

theorem sA_zero : sA 0 = Real.sqrt 2 / 2 := by
  rw [sA, prof_zero, Real.sin_pi_div_four]

theorem cA_zero : cA 0 = Real.sqrt 2 / 2 := by
  rw [cA, prof_zero, Real.cos_pi_div_four]

theorem sA_one : sA 1 = 1 / 2 := by
  rw [sA, prof_one, Real.sin_pi_div_six]

theorem cA_one : cA 1 = Real.sqrt 3 / 2 := by
  rw [cA, prof_one, Real.cos_pi_div_six]

theorem hasDerivAt_sA (t : ℝ) : HasDerivAt sA (cA t * profD t) t := by
  simpa [cA, mul_comm] using (Real.hasDerivAt_sin (prof t)).comp t (hasDerivAt_prof t)

theorem hasDerivAt_cA (t : ℝ) : HasDerivAt cA (-(sA t * profD t)) t := by
  simpa [sA, mul_comm] using (Real.hasDerivAt_cos (prof t)).comp t (hasDerivAt_prof t)

end MovingCircleProfile
