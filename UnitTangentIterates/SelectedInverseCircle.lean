import Mathlib
import UnitTangentIterates.SelectedInverseOval

/-!
# The selected inverse of a circle

The hypotheses of `SelectedInverseOval.exists_oval_rear_of_oval_front` are not
vacuous: they are satisfied by every circle of radius `r > 1`, whose curvature
is the constant `1/r ∈ (0,1)`.  This file checks that, and so exhibits a
concrete instance of the selected inverse.

* `circleFront` : the arclength parametrization `s ↦ r e^{is/r}` of the circle
  of radius `r`;
* `exists_oval_rear_of_circle` : for `r > 1` there is an oval `Y` with
  `range (𝒯 Y) = range (circleFront r)` — the circle of radius `r` is the
  unit-tangent transform of an oval, namely of the circle of radius `√(r²−1)`.
-/

noncomputable section

open Set Function

namespace SelectedInverseCircle

/-- The arclength parametrization of the circle of radius `r` centred at the
origin. -/
def circleFront (r : ℝ) : ℝ → ℂ := fun s => (r : ℂ) * Complex.exp (Complex.I * ((s / r : ℝ) : ℂ))

/-- The tangent angle of `circleFront r`. -/
def circleAngle (r : ℝ) : ℝ → ℝ := fun s => s / r + Real.pi / 2

theorem hasDerivAt_circleFront {r : ℝ} (hr : 0 < r) (s : ℝ) :
    HasDerivAt (circleFront r)
      (Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ))) s := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hbase : HasDerivAt (fun s : ℝ => Complex.I * ((s / r : ℝ) : ℂ))
      (Complex.I * (1 / r : ℂ)) s := by
    have h : HasDerivAt (fun s : ℝ => ((s / r : ℝ) : ℂ)) ((1 / r : ℂ)) s := by
      have := ((hasDerivAt_id s).div_const r).ofReal_comp
      simpa [one_div] using this
    exact h.const_mul Complex.I
  have h := (hbase.cexp).const_mul (r : ℂ)
  have hpi : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    push_cast
    simp
  have hsplit : ((circleAngle r s : ℝ) : ℂ)
      = ((s / r : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) := by
    rw [circleAngle]
    push_cast
    ring
  have hval : (r : ℂ) * (Complex.exp (Complex.I * ((s / r : ℝ) : ℂ))
      * (Complex.I * (1 / r : ℂ)))
      = Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ)) := by
    rw [hsplit, mul_add, Complex.exp_add, hpi]
    field_simp
  exact h.congr_deriv hval

theorem hasDerivAt_circleAngle {r : ℝ} (s : ℝ) :
    HasDerivAt (circleAngle r) (1 / r) s := by
  unfold circleAngle
  simpa using ((hasDerivAt_id s).div_const r).add_const (Real.pi / 2)

theorem periodic_circleFront {r : ℝ} (hr : 0 < r) :
    Periodic (circleFront r) (2 * Real.pi * r) := by
  intro s
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hstep : ((s + 2 * Real.pi * r) / r : ℝ) = s / r + 2 * Real.pi := by
    field_simp
  simp only [circleFront, hstep]
  push_cast
  rw [mul_add, Complex.exp_add]
  have h2pi : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = (2 * Real.pi : ℂ) * Complex.I by ring]
    simp
  rw [h2pi, mul_one]

/-- On one period the map `s ↦ e^{is/r}` is injective. -/
theorem injOn_expCircle {r : ℝ} (hr : 0 < r) :
    InjOn (fun s : ℝ => Complex.exp (Complex.I * ((s / r : ℝ) : ℂ)))
      (Ico 0 (2 * Real.pi * r)) := by
  intro s1 h1 s2 h2 he
  simp only at he
  rw [Complex.exp_eq_exp_iff_exists_int] at he
  obtain ⟨n, hn⟩ := he
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hn' : ((s1 / r : ℝ) : ℂ) = ((s2 / r : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have : Complex.I * ((s1 / r : ℝ) : ℂ)
        = Complex.I * (((s2 / r : ℝ) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) := by
      rw [hn]; ring
    exact mul_left_cancel₀ hI this
  have hreal : s1 / r = s2 / r + (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast hn'
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hs : s1 = s2 + (n : ℝ) * (2 * Real.pi * r) := by
    field_simp at hreal
    nlinarith [hreal]
  have hn0 : (n : ℝ) = 0 := by
    rcases h1 with ⟨h1a, h1b⟩
    rcases h2 with ⟨h2a, h2b⟩
    have hlt : |(n : ℝ)| < 1 := by
      rw [abs_lt]
      constructor
      · nlinarith [mul_pos hpi hr]
      · nlinarith [mul_pos hpi hr]
    have hnabs : (|n| : ℤ) < 1 := by
      have : ((|n| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hlt
      exact_mod_cast this
    have hz : n = 0 := Int.abs_lt_one_iff.mp hnabs
    simp [hz]
  rw [hs, hn0]
  ring

/-- **The rear track of a circle is embedded.**  For a constant steering angle
`d₀` the rear track of the circle of radius `r > 1` is again a circle (of
radius `|r − e^{i(π/2 − d₀)}| ≠ 0`), so it is injective on one period. -/
theorem injOn_rearTrack_circle {r : ℝ} (hr : 1 < r) (d0 : ℝ) :
    InjOn (RearTrack.rearTrack (circleFront r) (circleAngle r) (fun _ => d0))
      (Ico 0 (2 * Real.pi * r)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hform : ∀ s, RearTrack.rearTrack (circleFront r) (circleAngle r) (fun _ => d0) s
      = Complex.exp (Complex.I * ((s / r : ℝ) : ℂ))
        * ((r : ℂ) - Complex.exp (Complex.I * ((Real.pi / 2 - d0 : ℝ) : ℂ))) := by
    intro s
    simp only [RearTrack.rearTrack, circleFront, RearTrack.rearAngle, circleAngle]
    have : ((s / r + Real.pi / 2 - d0 : ℝ) : ℂ)
        = ((s / r : ℝ) : ℂ) + ((Real.pi / 2 - d0 : ℝ) : ℂ) := by push_cast; ring
    rw [this, mul_add, Complex.exp_add]
    ring
  have hwne : (r : ℂ) - Complex.exp (Complex.I * ((Real.pi / 2 - d0 : ℝ) : ℂ)) ≠ 0 := by
    intro hzero
    have hnorm : ‖(r : ℂ)‖ = ‖Complex.exp (Complex.I * ((Real.pi / 2 - d0 : ℝ) : ℂ))‖ := by
      rw [sub_eq_zero] at hzero
      rw [hzero]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      Complex.norm_exp] at hnorm
    simp at hnorm
    linarith
  intro s1 h1 s2 h2 heq
  rw [hform s1, hform s2] at heq
  exact injOn_expCircle hr0 h1 h2 (mul_right_cancel₀ hwne heq)

/-- **The circle of radius `r > 1` is the unit-tangent transform of an oval.**
This is an instance of `SelectedInverseOval.exists_oval_rear_of_oval_front`,
and shows that its hypotheses are satisfiable. -/
theorem exists_oval_rear_of_circle {r : ℝ} (hr : 1 < r) :
    ∃ Y : ℝ → ℂ, MainTheoremConditional.IsOval Y ∧
      range (UnitTangent.unitTangentMap Y) = range (circleFront r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  set p : ℝ := 2 * Real.pi * r with hp
  have hppos : 0 < p := by
    have : 0 < Real.pi := Real.pi_pos
    positivity
  have hkap1 : 1 / r < 1 := by
    rw [div_lt_one hr0]; exact hr
  have hkmin : 0 < 1 / r := by positivity
  -- the constant steering angle
  set d0 : ℝ := Real.arcsin (1 / r) with hd0
  have hsin : Real.sin d0 = 1 / r := Real.sin_arcsin (by linarith) hkap1.le
  have hd0nonneg : 0 ≤ d0 := Real.arcsin_nonneg.mpr hkmin.le
  have hd0le : d0 ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  -- uniqueness pins any admissible steering angle to `d0`
  have huniq : ∀ delta : ℝ → ℝ, Periodic delta p →
      (∀ s, delta s ∈ Icc 0 (Real.arcsin (1 / r))) →
      (∀ s, HasDerivAt delta (1 / r - Real.sin (delta s)) s) → delta = fun _ => d0 := by
    intro delta hper hmem hode
    refine Shadowing.steering_unique (K := fun _ => 1 / r) hppos hode ?_ hper
      (fun s => by simp) ?_ ?_
    · intro s
      simpa [hsin] using (hasDerivAt_const s d0)
    · intro s
      exact ⟨by linarith [(hmem s).1], le_trans (hmem s).2 hd0le⟩
    · exact fun s => ⟨by linarith, hd0le⟩
  refine SelectedInverseOval.exists_oval_rear_of_oval_front (Θ := circleAngle r)
    (K := fun _ => 1 / r) (kmin := 1 / r) (kap := 1 / r) hppos hkmin hkap1
    continuous_const (fun _ => rfl) (hasDerivAt_circleFront hr0)
    (fun s => hasDerivAt_circleAngle s) (periodic_circleFront hr0)
    (fun _ => le_refl _) (fun _ => le_refl _) ?_ |>.imp
    (fun Y hY => by
      obtain ⟨_, _, _, hoval, hrange, _⟩ := hY
      exact ⟨hoval, hrange⟩)
  -- the rear track of the circle is a circle of radius `√(r²-1)`, hence embedded
  intro delta hper hmem hode
  rw [huniq delta hper hmem hode]
  exact injOn_rearTrack_circle hr d0

end SelectedInverseCircle
