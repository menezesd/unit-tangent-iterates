import Mathlib
import UnitTangentIterates.GaugeFrameTimeBounds

/-!
# Non-vacuity of the normal-flow relations, on a family that deforms

`GaugeFrameTimeBounds.angleRate_eq` and `GaugeFrameTimeBounds.curvRate_eq`
derive the rates at which the tangent angle and the curvature of a family of
curves move, from the motion of the family and from the identity `∂_sξ = kη`
that preserves the arclength parametrization.  This file checks the whole
hypothesis block on a family whose shape really changes: the circle of radius
`e^t`, carried in its own arclength,

```
  Y(t,s) = e^t e^{i s e^{−t}} ,   α(t,s) = s e^{−t} + π/2 ,   k(t,s) = e^{−t} ,
```

which dilates at unit logarithmic rate.  Its velocity splits as

```
  ∂_t Y = ξ e^{iα} + η · i e^{iα} ,   ξ(t,s) = −s ,   η(t,s) = −e^t ,
```

— the tangential rate `−s` is what keeps the arclength parametrization, and
indeed `∂_sξ = −1 = k η`.  The two relations then read `∂_tα = −s e^{−t}` and
`∂_t k = −e^{−t}`, which is what the direct computation gives.

Main results: `hasDerivAt_Ydil_space`, `hasDerivAt_Ydil_time`,
`angleRate_dilation`, `curvRate_dilation`.
-/

noncomputable section

open Complex

namespace GaugeFrameTimeBoundsDilation

/-- The dilating circle, carried in its own arclength. -/
def Ydil (t s : ℝ) : ℂ :=
  (Real.exp t : ℂ) * Complex.exp (Complex.I * ((s * Real.exp (-t) : ℝ) : ℂ))

/-- Its tangent angle. -/
def alphaDil (t s : ℝ) : ℝ := s * Real.exp (-t) + Real.pi / 2

/-- Its curvature. -/
def kDil (t : ℝ) : ℝ := Real.exp (-t)

/-- The tangential rate of its motion. -/
def xiDil (s : ℝ) : ℝ := -s

/-- The normal rate of its motion. -/
def etaDil (t : ℝ) : ℝ := -Real.exp t

/-- The rate at which the tangent angle turns. -/
def alphaTDil (t s : ℝ) : ℝ := -(s * Real.exp (-t))

/-- The rate at which the curvature moves. -/
def kTDil (t : ℝ) : ℝ := -Real.exp (-t)

theorem exp_I_pi_div_two : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  have h : Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    ring
  rw [h, Complex.exp_mul_I]
  have h1 : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.cos_pi_div_two
  have h2 : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.sin_pi_div_two
  rw [h1, h2, one_mul, zero_add]

/-- The unit tangent, written with the tangent angle. -/
theorem exp_alphaDil (t s : ℝ) :
    Complex.exp (Complex.I * (alphaDil t s : ℂ))
      = Complex.I * Complex.exp (Complex.I * ((s * Real.exp (-t) : ℝ) : ℂ)) := by
  have hsplit : Complex.exp (Complex.I * (alphaDil t s : ℂ))
      = Complex.exp (Complex.I * ((s * Real.exp (-t) : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, alphaDil]
    congr 1
    push_cast
    ring
  rw [hsplit, exp_I_pi_div_two]
  ring

/-- **The dilating circle is carried in its own arclength.** -/
theorem hasDerivAt_Ydil_space (t s : ℝ) :
    HasDerivAt (Ydil t) (Complex.exp (Complex.I * (alphaDil t s : ℂ))) s := by
  have hinner : HasDerivAt (fun x : ℝ => Complex.I * ((x * Real.exp (-t) : ℝ) : ℂ))
      (Complex.I * ((Real.exp (-t) : ℝ) : ℂ)) s := by
    simpa using (((hasDerivAt_id s).mul_const (Real.exp (-t))).ofReal_comp).const_mul Complex.I
  have h := (hinner.cexp).const_mul (Real.exp t : ℂ)
  refine h.congr_deriv ?_
  rw [exp_alphaDil]
  have hexp : (Real.exp t : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero t)]
    norm_num
  linear_combination (Complex.I * Complex.exp (Complex.I * ((s * Real.exp (-t) : ℝ) : ℂ))) * hexp

/-- **The motion of the dilating circle**, split into its tangential and normal
components. -/
theorem hasDerivAt_Ydil_time (t s : ℝ) :
    HasDerivAt (fun r => Ydil r s)
      ((xiDil s : ℂ) * Complex.exp (Complex.I * (alphaDil t s : ℂ))
        + (etaDil t : ℂ) * (Complex.I * Complex.exp (Complex.I * (alphaDil t s : ℂ)))) t := by
  have hexpt : HasDerivAt (fun r : ℝ => ((Real.exp r : ℝ) : ℂ)) ((Real.exp t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_exp t).ofReal_comp
  have hneg : HasDerivAt (fun r : ℝ => s * Real.exp (-r)) (s * -Real.exp (-t)) t := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-t)) t := by
      simpa using (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
    exact h.const_mul s
  have hinner : HasDerivAt (fun r : ℝ => Complex.I * ((s * Real.exp (-r) : ℝ) : ℂ))
      (Complex.I * ((s * -Real.exp (-t) : ℝ) : ℂ)) t :=
    (hneg.ofReal_comp).const_mul Complex.I
  have h := hexpt.mul hinner.cexp
  refine h.congr_deriv ?_
  rw [exp_alphaDil, xiDil, etaDil]
  have hexp : (Real.exp t : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero t)]
    norm_num
  set E := Complex.exp (Complex.I * ((s * Real.exp (-t) : ℝ) : ℂ)) with hE
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  linear_combination (-(Complex.I * (s : ℂ) * E)) * hexp + (((Real.exp t : ℝ) : ℂ) * E) * hI

/-! ### The two relations, verified -/

/-- The derivative of the tangent angle in the arclength is the curvature. -/
theorem hasDerivAt_alphaDil_space (t x : ℝ) : HasDerivAt (alphaDil t) (kDil t) x := by
  have h : HasDerivAt (fun y : ℝ => y * Real.exp (-t) + Real.pi / 2) (Real.exp (-t)) x := by
    simpa using ((hasDerivAt_id x).mul_const (Real.exp (-t))).add_const (Real.pi / 2)
  exact h

/-- The derivative of the tangent angle in the time. -/
theorem hasDerivAt_alphaDil_time (t s : ℝ) :
    HasDerivAt (fun r : ℝ => alphaDil r s) (alphaTDil t s) t := by
  have h1 : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-t)) t := by
    simpa using (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  have h2 := (h1.const_mul s).add_const (Real.pi / 2)
  have heq : s * -Real.exp (-t) = alphaTDil t s := by rw [alphaTDil]; ring
  rw [← heq]
  exact h2

/-- The tangential rate keeps the arclength parametrization: `∂_sξ = kη`. -/
theorem hasDerivAt_xiDil (t x : ℝ) : HasDerivAt xiDil (kDil t * etaDil t) x := by
  have hk : kDil t * etaDil t = -1 := by
    rw [kDil, etaDil, Real.exp_neg]
    field_simp
  rw [hk]
  simpa [xiDil] using (hasDerivAt_id x).neg

/-- The unit tangent turns at the rate `i ∂_tα`. -/
theorem hasDerivAt_tangent_time (t s : ℝ) :
    HasDerivAt (fun r => Complex.exp (Complex.I * (alphaDil r s : ℂ)))
      (Complex.I * ((alphaTDil t s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alphaDil t s : ℂ))) t := by
  have h1 : HasDerivAt (fun r => Complex.I * ((alphaDil r s : ℝ) : ℂ))
      (Complex.I * ((alphaTDil t s : ℝ) : ℂ)) t :=
    (hasDerivAt_alphaDil_time t s).ofReal_comp.const_mul Complex.I
  simpa [mul_comm, mul_assoc] using h1.cexp

/-- The unit tangent turns at the rate `i k` in the arclength. -/
theorem hasDerivAt_tangent_space (t x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (alphaDil t y : ℂ)))
      (Complex.I * ((kDil t : ℝ) : ℂ) * Complex.exp (Complex.I * (alphaDil t x : ℂ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * ((alphaDil t y : ℝ) : ℂ))
      (Complex.I * ((kDil t : ℝ) : ℂ)) x :=
    (hasDerivAt_alphaDil_space t x).ofReal_comp.const_mul Complex.I
  simpa [mul_comm, mul_assoc] using h1.cexp

/-- The arclength derivative of the velocity is the time derivative of the unit
tangent: the equality of the mixed partial derivatives, here by computation. -/
theorem hasDerivAt_velocity_space (t s : ℝ) :
    HasDerivAt (fun x : ℝ => ((xiDil x : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alphaDil t x : ℂ))
        + ((etaDil t : ℝ) : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (alphaDil t x : ℂ))))
      (Complex.I * ((alphaTDil t s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alphaDil t s : ℂ))) s := by
  have hxi : HasDerivAt (fun x : ℝ => ((xiDil x : ℝ) : ℂ)) (((-1 : ℝ) : ℝ) : ℂ) s := by
    have h : HasDerivAt xiDil (-1 : ℝ) s := by
      simpa [xiDil] using (hasDerivAt_id s).neg
    exact h.ofReal_comp
  have hsum := (hxi.mul (hasDerivAt_tangent_space t s)).add
    (((hasDerivAt_tangent_space t s).const_mul Complex.I).const_mul ((etaDil t : ℝ) : ℂ))
  refine hsum.congr_deriv ?_
  have hke : kDil t * etaDil t = -1 := by
    rw [kDil, etaDil, Real.exp_neg]
    field_simp
  have hkeC : ((kDil t : ℝ) : ℂ) * ((etaDil t : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_mul, hke]
    norm_num
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have halpha : ((alphaTDil t s : ℝ) : ℂ) = ((kDil t : ℝ) : ℂ) * ((xiDil s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [alphaTDil, kDil, xiDil]
    ring
  rw [halpha]
  set E := Complex.exp (Complex.I * (alphaDil t s : ℂ)) with hE
  push_cast
  linear_combination (((etaDil t : ℝ) : ℂ) * ((kDil t : ℝ) : ℂ) * E) * hI + (-E) * hkeC

/-- **The tangent angle of the dilating circle turns at the rate `∂_sη + kξ`**,
as `GaugeFrameTimeBounds.angleRate_eq` predicts. -/
theorem angleRate_dilation (t s : ℝ) : alphaTDil t s = 0 + kDil t * xiDil s :=
  GaugeFrameTimeBounds.angleRate_eq (alpha := alphaDil) (k := fun t _ => kDil t)
    (xi := fun _ s => xiDil s) (eta := fun t _ => etaDil t) (etaS := fun _ _ => 0)
    (alphaT := alphaTDil) t s (hasDerivAt_alphaDil_space t)
    (fun x => hasDerivAt_const x (etaDil t)) (hasDerivAt_xiDil t)
    (hasDerivAt_alphaDil_time t s) (hasDerivAt_tangent_time t s)
    (hasDerivAt_velocity_space t s)

/-- **The curvature of the dilating circle moves at the rate
`∂_s²η + k²η + ξ ∂_s k`**, as `GaugeFrameTimeBounds.curvRate_eq` predicts. -/
theorem curvRate_dilation (t s : ℝ) :
    kTDil t = 0 + kDil t ^ 2 * etaDil t + xiDil s * 0 :=
  GaugeFrameTimeBounds.curvRate_eq (k := fun t _ => kDil t) (xi := fun _ s => xiDil s)
    (eta := fun t _ => etaDil t) (etaS := fun _ _ => 0) (etaSS := fun _ _ => 0)
    (kX := fun _ _ => 0) (alphaT := alphaTDil) (kT := fun t _ => kTDil t) t s
    (fun x => by simp only [alphaTDil, kDil, xiDil]; ring)
    (fun x => hasDerivAt_const x (0 : ℝ)) (fun x => hasDerivAt_const x (kDil t))
    (hasDerivAt_xiDil t)
    (by
      have h : HasDerivAt (fun y : ℝ => -(y * Real.exp (-t))) (-Real.exp (-t)) s := by
        simpa using ((hasDerivAt_id s).mul_const (Real.exp (-t))).neg
      simpa [alphaTDil, kTDil] using h)

/-- The time derivative of the curvature is indeed `kTDil`. -/
theorem hasDerivAt_kDil_time (t : ℝ) : HasDerivAt kDil (kTDil t) t := by
  have h : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-t)) t := by
    simpa using (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  simpa [kDil, kTDil] using h

end GaugeFrameTimeBoundsDilation
