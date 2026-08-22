import Mathlib

/-!
# An explicit admissible pulse: `y(s) = A·sech²(λs)`

The hypothesis block of a matching configuration (`ModelOrbitDefect.Config`)
asks for a *steering pulse of the previous model*: a nonnegative function on the
line which decays exponentially, whose first two derivatives are dominated by
the function itself with small constants, and whose total mass is `π`.

This file provides the explicit family `A·sech²(λ s)` and verifies all of those
properties:

* `hasDerivAt_pulse`, `hasDerivAt_pulseD` — the first two derivatives;
* `abs_pulseD_le`, `abs_pulseD2_le` — the relative derivative bounds
  `|y'| ≤ 2λ y`, `|y''| ≤ 8λ² y`;
* `pulse_le`, `pulse_le_exp` — the sup bound `y ≤ A` and the exponential
  majorant `y ≤ 4A e^{-2λ|s|}`;
* `integral_pulse` — the mass `∫_ℝ y = 2A/λ`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace SechPulse

/-- The pulse `y(s) = A·sech²(λ s)`. -/
def pulse (A lam : ℝ) : ℝ → ℝ := fun s => A / Real.cosh (lam * s) ^ 2

/-- Its derivative, `y'(s) = -2Aλ·sinh(λs)/cosh³(λs)`. -/
def pulseD (A lam : ℝ) : ℝ → ℝ := fun s =>
  -2 * A * lam * Real.sinh (lam * s) / Real.cosh (lam * s) ^ 3

/-- Its second derivative,
`y''(s) = 2Aλ²(3·sinh²(λs) − cosh²(λs))/cosh⁴(λs)`. -/
def pulseD2 (A lam : ℝ) : ℝ → ℝ := fun s =>
  2 * A * lam ^ 2 * (3 * Real.sinh (lam * s) ^ 2 - Real.cosh (lam * s) ^ 2)
    / Real.cosh (lam * s) ^ 4

variable {A lam : ℝ}

/-- `|sinh| ≤ cosh`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  nlinarith [Real.cosh_sq_sub_sinh_sq x, Real.cosh_pos x, abs_nonneg (Real.sinh x),
    sq_abs (Real.sinh x)]

/-- The pulse is nonnegative for a nonnegative amplitude. -/
theorem pulse_nonneg (hA : 0 ≤ A) (s : ℝ) : 0 ≤ pulse A lam s :=
  div_nonneg hA (sq_nonneg _)

/-- The pulse is bounded by its amplitude. -/
theorem pulse_le (hA : 0 ≤ A) (s : ℝ) : pulse A lam s ≤ A := by
  have h1 : (1:ℝ) ≤ Real.cosh (lam * s) := Real.one_le_cosh _
  have h2 : (1:ℝ) ≤ Real.cosh (lam * s) ^ 2 := by nlinarith
  rw [pulse, div_le_iff₀ (by positivity)]
  nlinarith

/-- The first derivative. -/
theorem hasDerivAt_pulse (s : ℝ) : HasDerivAt (pulse A lam) (pulseD A lam s) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.cosh (lam * s)) (Real.sinh (lam * s) * lam) s := by
    simpa using (Real.hasDerivAt_cosh (lam * s)).comp s ((hasDerivAt_id s).const_mul lam)
  have hc : HasDerivAt (fun s : ℝ => Real.cosh (lam * s) ^ 2)
      (2 * Real.cosh (lam * s) ^ 1 * (Real.sinh (lam * s) * lam)) s := h1.pow 2
  have hne : Real.cosh (lam * s) ^ 2 ≠ 0 := by positivity
  have h := (hasDerivAt_const s A).div hc hne
  convert h using 1
  rw [pulseD]
  have hcpos : (0:ℝ) < Real.cosh (lam * s) := Real.cosh_pos _
  field_simp
  ring

/-- The second derivative. -/
theorem hasDerivAt_pulseD (s : ℝ) : HasDerivAt (pulseD A lam) (pulseD2 A lam s) s := by
  have hs : HasDerivAt (fun s : ℝ => Real.sinh (lam * s)) (Real.cosh (lam * s) * lam) s := by
    simpa using (Real.hasDerivAt_sinh (lam * s)).comp s ((hasDerivAt_id s).const_mul lam)
  have hc : HasDerivAt (fun s : ℝ => Real.cosh (lam * s)) (Real.sinh (lam * s) * lam) s := by
    simpa using (Real.hasDerivAt_cosh (lam * s)).comp s ((hasDerivAt_id s).const_mul lam)
  have hnum : HasDerivAt (fun s : ℝ => -2 * A * lam * Real.sinh (lam * s))
      (-2 * A * lam * (Real.cosh (lam * s) * lam)) s := hs.const_mul _
  have hden : HasDerivAt (fun s : ℝ => Real.cosh (lam * s) ^ 3)
      (3 * Real.cosh (lam * s) ^ 2 * (Real.sinh (lam * s) * lam)) s := hc.pow 3
  have hne : Real.cosh (lam * s) ^ 3 ≠ 0 := by positivity
  have h := hnum.div hden hne
  convert h using 1
  rw [pulseD2]
  have hcpos : (0:ℝ) < Real.cosh (lam * s) := Real.cosh_pos _
  have hid : Real.cosh (lam * s) ^ 2 - Real.sinh (lam * s) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  field_simp
  nlinarith [hid, sq_nonneg (Real.cosh (lam * s)), sq_nonneg (Real.sinh (lam * s))]

/-- The relative bound for the first derivative: `|y'| ≤ 2λ y`. -/
theorem abs_pulseD_le (hA : 0 ≤ A) (hlam : 0 ≤ lam) (s : ℝ) :
    |pulseD A lam s| ≤ 2 * lam * pulse A lam s := by
  have hcpos : (0:ℝ) < Real.cosh (lam * s) := Real.cosh_pos _
  have hsc : |Real.sinh (lam * s)| ≤ Real.cosh (lam * s) := abs_sinh_le_cosh _
  have hrw : 2 * lam * pulse A lam s
      = 2 * lam * A * Real.cosh (lam * s) / Real.cosh (lam * s) ^ 3 := by
    rw [pulse]; field_simp
  rw [pulseD, hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cosh (lam * s) ^ 3)]
  gcongr
  have habs : |(-2 : ℝ) * A * lam * Real.sinh (lam * s)|
      = 2 * A * lam * |Real.sinh (lam * s)| := by
    rw [show (-2 : ℝ) * A * lam * Real.sinh (lam * s)
      = -(2 * A * lam) * Real.sinh (lam * s) by ring, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * A * lam)]
  rw [habs]
  nlinarith [mul_le_mul_of_nonneg_left hsc (by positivity : (0:ℝ) ≤ 2 * A * lam)]

/-- The relative bound for the second derivative: `|y''| ≤ 8λ² y`. -/
theorem abs_pulseD2_le (hA : 0 ≤ A) (s : ℝ) :
    |pulseD2 A lam s| ≤ 8 * lam ^ 2 * pulse A lam s := by
  have hcpos : (0:ℝ) < Real.cosh (lam * s) := Real.cosh_pos _
  have hid : Real.sinh (lam * s) ^ 2 = Real.cosh (lam * s) ^ 2 - 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (lam * s)]
  have hnum : |3 * Real.sinh (lam * s) ^ 2 - Real.cosh (lam * s) ^ 2|
      ≤ 4 * Real.cosh (lam * s) ^ 2 := by
    rw [hid, abs_le]
    constructor <;> nlinarith [sq_nonneg (Real.cosh (lam * s)), hcpos]
  have hrw : 8 * lam ^ 2 * pulse A lam s
      = 8 * lam ^ 2 * A * Real.cosh (lam * s) ^ 2 / Real.cosh (lam * s) ^ 4 := by
    rw [pulse]; field_simp
  rw [pulseD2, hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cosh (lam * s) ^ 4)]
  gcongr
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * A * lam ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ 2 * A * lam ^ 2)]

/-- `e^{|x|} ≤ 2cosh x`. -/
theorem exp_abs_le_two_mul_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
    field_simp
    linarith
  · rw [h]
    have : (0:ℝ) < Real.exp x := Real.exp_pos _
    field_simp
    linarith

/-- The exponential majorant `y ≤ 4A e^{-2λ|s|}` for `λ ≥ 0`. -/
theorem pulse_le_exp (hA : 0 ≤ A) (hlam : 0 ≤ lam) (s : ℝ) :
    pulse A lam s ≤ 4 * A * Real.exp (-(2 * lam) * |s|) := by
  have hcpos : (0:ℝ) < Real.cosh (lam * s) := Real.cosh_pos _
  have habs : |lam * s| = lam * |s| := by rw [abs_mul, abs_of_nonneg hlam]
  have hex : Real.exp (lam * |s|) ≤ 2 * Real.cosh (lam * s) := by
    have := exp_abs_le_two_mul_cosh (lam * s)
    rwa [habs] at this
  have hsq : Real.exp (2 * lam * |s|) ≤ 4 * Real.cosh (lam * s) ^ 2 := by
    have h1 : Real.exp (2 * lam * |s|) = Real.exp (lam * |s|) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h1]
    nlinarith [Real.exp_pos (lam * |s|)]
  have hmul : Real.exp (-(2 * lam) * |s|) * Real.exp (2 * lam * |s|) = 1 := by
    rw [← Real.exp_add, show -(2 * lam) * |s| + 2 * lam * |s| = 0 by ring, Real.exp_zero]
  have h4 : 1 ≤ 4 * Real.cosh (lam * s) ^ 2 * Real.exp (-(2 * lam) * |s|) := by
    nlinarith [Real.exp_pos (-(2 * lam) * |s|), hsq]
  rw [pulse, div_le_iff₀ (by positivity)]
  nlinarith [h4, hA]

/-- The pulse is continuous. -/
theorem continuous_pulse : Continuous (pulse A lam) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_pulse (A := A) (lam := lam) s).continuousAt

/-- Its derivative is continuous. -/
theorem continuous_pulseD : Continuous (pulseD A lam) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_pulseD (A := A) (lam := lam) s).continuousAt

/-- Its second derivative is continuous. -/
theorem continuous_pulseD2 : Continuous (pulseD2 A lam) := by
  have h : (pulseD2 A lam) = fun s => 2 * A * lam ^ 2 *
      (3 * Real.sinh (lam * s) ^ 2 - Real.cosh (lam * s) ^ 2) / Real.cosh (lam * s) ^ 4 := rfl
  rw [h]
  exact (by fun_prop : Continuous fun s : ℝ => 2 * A * lam ^ 2 *
    (3 * Real.sinh (lam * s) ^ 2 - Real.cosh (lam * s) ^ 2)).div
    (by fun_prop) fun s => by positivity

/-! ### The mass of the pulse -/

/-- The antiderivative `(A/λ)·tanh(λ s)` of the pulse. -/
def primitive (A lam : ℝ) : ℝ → ℝ := fun s =>
  A / lam * (Real.sinh (lam * s) / Real.cosh (lam * s))

theorem hasDerivAt_primitive (hlam : 0 < lam) (s : ℝ) :
    HasDerivAt (primitive A lam) (pulse A lam s) s := by
  have hs : HasDerivAt (fun s : ℝ => Real.sinh (lam * s)) (Real.cosh (lam * s) * lam) s := by
    simpa using (Real.hasDerivAt_sinh (lam * s)).comp s ((hasDerivAt_id s).const_mul lam)
  have hc : HasDerivAt (fun s : ℝ => Real.cosh (lam * s)) (Real.sinh (lam * s) * lam) s := by
    simpa using (Real.hasDerivAt_cosh (lam * s)).comp s ((hasDerivAt_id s).const_mul lam)
  have hne : Real.cosh (lam * s) ≠ 0 := (Real.cosh_pos _).ne'
  have h := (hs.div hc hne).const_mul (A / lam)
  convert h using 1
  rw [pulse]
  have hid : Real.sinh (lam * s) ^ 2 = Real.cosh (lam * s) ^ 2 - 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (lam * s)]
  field_simp
  rw [hid]
  ring

theorem tendsto_primitive_atTop (hlam : 0 < lam) :
    Tendsto (primitive A lam) atTop (nhds (A / lam)) := by
  have htanh : Tendsto (fun s : ℝ => Real.sinh (lam * s) / Real.cosh (lam * s))
      atTop (nhds 1) := by
    have heq : ∀ s : ℝ, Real.sinh (lam * s) / Real.cosh (lam * s)
        = (1 - Real.exp (-(2 * (lam * s)))) / (1 + Real.exp (-(2 * (lam * s)))) := by
      intro s
      rw [Real.sinh_eq, Real.cosh_eq,
        show -(2 * (lam * s)) = -(lam * s) + -(lam * s) by ring, Real.exp_add, Real.exp_neg]
      have hpos : (0:ℝ) < Real.exp (lam * s) := Real.exp_pos _
      field_simp
    have hexp : Tendsto (fun s : ℝ => Real.exp (-(2 * (lam * s)))) atTop (nhds 0) := by
      have h1 : Tendsto (fun s : ℝ => 2 * (lam * s)) atTop atTop := by
        have : Tendsto (fun s : ℝ => (2 * lam) * s) atTop atTop :=
          Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
        simpa [mul_assoc] using this
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have hlim := ((tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℝ))).sub hexp).div
      ((tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℝ))).add hexp) (by norm_num)
    simp only [sub_zero, add_zero, div_one] at hlim
    exact hlim.congr fun s => (heq s).symm
  have := htanh.const_mul (A / lam)
  simpa [primitive] using this

theorem tendsto_primitive_atBot (hlam : 0 < lam) :
    Tendsto (primitive A lam) atBot (nhds (-(A / lam))) := by
  have hodd : ∀ s : ℝ, primitive A lam (-s) = -primitive A lam s := by
    intro s
    simp [primitive, Real.sinh_neg, Real.cosh_neg, mul_neg, neg_div]
  have h := (tendsto_primitive_atTop (A := A) (lam := lam) hlam).neg
  have h2 : Tendsto (fun s : ℝ => -primitive A lam (-s)) atBot (nhds (-(A / lam))) :=
    h.comp tendsto_neg_atBot_atTop
  refine h2.congr fun s => ?_
  rw [hodd s]
  ring

/-- `s ↦ e^{-b|s|}` is integrable on the line, for `b > 0`. -/
theorem integrable_exp_neg_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ => Real.exp (-b * |s|)) := by
  have h1 : IntegrableOn (fun s : ℝ => Real.exp (-b * |s|)) (Iic 0) volume := by
    refine IntegrableOn.congr_fun (integrableOn_exp_mul_Iic hb 0) ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only []
    rw [abs_of_nonpos hx']; ring_nf
  have h2 : IntegrableOn (fun s : ℝ => Real.exp (-b * |s|)) (Ioi 0) volume := by
    refine IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi 0 hb) ?_ measurableSet_Ioi
    intro x hx
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    simp only []
    rw [abs_of_nonneg hx']
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The pulse is integrable. -/
theorem integrable_pulse (hA : 0 ≤ A) (hlam : 0 < lam) : Integrable (pulse A lam) := by
  have hmaj : Integrable (fun s : ℝ => 4 * A * Real.exp (-(2 * lam) * |s|)) :=
    (integrable_exp_neg_abs (by positivity : (0:ℝ) < 2 * lam)).const_mul (4 * A)
  refine Integrable.mono' hmaj continuous_pulse.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pulse_nonneg hA s)]
  exact pulse_le_exp hA hlam.le s

/-- **The mass of the pulse**: `∫_ℝ A·sech²(λ s) ds = 2A/λ`. -/
theorem integral_pulse (hA : 0 ≤ A) (hlam : 0 < lam) :
    ∫ s : ℝ, pulse A lam s = 2 * (A / lam) := by
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (f := primitive A lam) (f' := pulse A lam)
    (fun x => hasDerivAt_primitive hlam x) (integrable_pulse hA hlam)
    (tendsto_primitive_atBot hlam) (tendsto_primitive_atTop hlam)
  rw [h]; ring

end SechPulse
