import Mathlib
import UnitTangentIterates.MovingCircleProfile
import UnitTangentIterates.RearOwnMotion

/-!
# The front data of a circle whose radius moves

Building on the steering profile `A(t)` of `MovingCircleProfile.lean`, this file
sets up the family of fronts

```
  F(t, s) = −i · (1 / sin A(t)) · e^{i s sin A(t)} ,
```

the circle of radius `R(t) = 1 / sin A(t)` traversed at unit speed, together
with all the data the path-distance assembly of
`RearOwnPathDistFrameDrift.lean` asks for: the tangent angle `Θ(t,s) = s sin A(t)`,
the curvature `K = sin A(t)`, the selected steering angle `δ(t,s) = A(t)`, the
arclength period `P(t) = 2π / sin A(t)`, the change of variable
`s_f(t,x) = x / cos A(t)` from the rear arclength, and the derivatives of all of
these in both variables.

Because the family is written in the arclength of each slice and the slices
change length, the marked point slides: the time derivative `Ḟ` has a
tangential part growing linearly in `s`.  That is exactly the drift the frame
bundle of `RearOwnFrameDrift.lean` was built to tolerate.

The rear of the slice at time `t` is the circle of radius `cos A(t) / sin A(t)`,
of length `Q(t) = 2π cos A(t)/ sin A(t)`: it moves from `2π` at `t = 0` to
`2π√3` at `t = 1`.

Main results: the derivative and periodicity lemmas used by
`MovingCirclePathDist.lean`, and `rearPeriod_zero`, `rearPeriod_one`.
-/

noncomputable section

open Set Function Complex RearTrack RearFamilyFrame RearOwnArclength RearOwnMotion
  MovingCircleProfile UniformFrameBounds

namespace MovingCircle

/-! ### The data -/

/-- The tangent angle of the front. -/
def Th : ℝ → ℝ → ℝ := fun t s => s * sA t

/-- The selected steering angle: the constant `A(t)`. -/
def de : ℝ → ℝ → ℝ := fun t _ => prof t

/-- The front: the circle of radius `1 / sin A(t)`, at unit speed. -/
def Ff : ℝ → ℝ → ℂ := fun t s =>
  -Complex.I * ((1 / sA t : ℝ) : ℂ) * Complex.exp (Complex.I * (Th t s : ℂ))

/-- The arclength period of the front. -/
def Pp : ℝ → ℝ := fun t => 2 * Real.pi / sA t

/-- The change of variable from the rear arclength to the front arclength. -/
def sff : ℝ → ℝ → ℝ := fun t x => x / cA t

/-- The curvature of the front. -/
def Kk : ℝ → ℝ → ℝ := fun t _ => sA t

/-- The time derivative of the tangent angle. -/
def Thdot : ℝ → ℝ → ℝ := fun t s => s * (cA t * profD t)

/-- Its arclength derivative. -/
def Thdots : ℝ → ℝ → ℝ := fun t _ => cA t * profD t

/-- The time derivative of the steering angle. -/
def ww : ℝ → ℝ → ℝ := fun t _ => profD t

/-- The time derivative of the front. -/
def Fdotf : ℝ → ℝ → ℂ := fun t s =>
  -Complex.I * Complex.exp (Complex.I * (Th t s : ℂ)) * ((cA t * profD t : ℝ) : ℂ)
    * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))

/-- Its arclength derivative. -/
def Fdotsf : ℝ → ℝ → ℂ := fun t s =>
  Complex.I * ((s * (cA t * profD t) : ℝ) : ℂ) * Complex.exp (Complex.I * (Th t s : ℂ))

/-- The time derivative of the change of variable. -/
def sfft : ℝ → ℝ → ℝ := fun t x => x * (sA t * profD t) / (cA t) ^ 2

/-- The normal velocity of the front. -/
def etaFf : ℝ → ℝ → ℝ := fun t _ => cA t * profD t / (sA t) ^ 2

/-- The velocity of the family of rears, written in the rear arclength. -/
def Ydotf : ℝ → ℝ → ℂ := fun t x =>
  trackVelocity Fdotf Thdot ww Th de t (sff t x) + (sfft t x) •
    ((Real.cos (de t (sff t x)) : ℂ)
      * Complex.exp (Complex.I * (rearAngle (Th t) (de t) (sff t x) : ℂ)))

/-! ### The arclength derivatives -/

theorem hasDerivAt_Th_space (t s : ℝ) : HasDerivAt (Th t) (sA t) s := by
  simpa [Th] using (hasDerivAt_id s).mul_const (sA t)

theorem hasDerivAt_ofReal_Th (t s : ℝ) :
    HasDerivAt (fun y : ℝ => ((Th t y : ℝ) : ℂ)) ((sA t : ℂ)) s := by
  simpa using (hasDerivAt_Th_space t s).ofReal_comp

theorem hasDerivAt_Ff_space (t s : ℝ) :
    HasDerivAt (Ff t) (Complex.exp (Complex.I * (Th t s : ℂ))) s := by
  have h1 := ((hasDerivAt_ofReal_Th t s).const_mul Complex.I).cexp
  have h2 := h1.const_mul (-Complex.I * ((1 / sA t : ℝ) : ℂ))
  refine h2.congr_deriv ?_
  have hs : ((sA t : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (sA_ne t))
  field_simp
  rw [Complex.I_sq]
  push_cast
  field_simp

theorem hasDerivAt_de_space (t s : ℝ) :
    HasDerivAt (de t) (Kk t s - Real.sin (de t s)) s := by
  have h : Kk t s - Real.sin (de t s) = 0 := by simp [Kk, de, sA]
  rw [h]
  exact hasDerivAt_const s (prof t)

/-! ### The time derivatives -/

theorem hasDerivAt_Th_time (t s : ℝ) : HasDerivAt (fun r => Th r s) (Thdot t s) t := by
  simpa [Th, Thdot, mul_comm] using (hasDerivAt_sA t).const_mul s

theorem hasDerivAt_de_time (t s : ℝ) : HasDerivAt (fun r => de r s) (ww t s) t :=
  hasDerivAt_prof t

theorem hasDerivAt_invsA (t : ℝ) :
    HasDerivAt (fun r => (1 / sA r : ℝ)) (-(cA t * profD t) / (sA t) ^ 2) t := by
  simpa using ((hasDerivAt_sA t).inv (sA_ne t)).congr_deriv (by
    field_simp)

theorem hasDerivAt_Ff_time (t s : ℝ) : HasDerivAt (fun r => Ff r s) (Fdotf t s) t := by
  have hg : HasDerivAt (fun r => ((1 / sA r : ℝ) : ℂ))
      (((-(cA t * profD t) / (sA t) ^ 2 : ℝ) : ℂ)) t := (hasDerivAt_invsA t).ofReal_comp
  have hth : HasDerivAt (fun r => ((Th r s : ℝ) : ℂ)) (((Thdot t s : ℝ) : ℂ)) t :=
    (hasDerivAt_Th_time t s).ofReal_comp
  have hh := (hth.const_mul Complex.I).cexp
  have h := (hg.const_mul (-Complex.I)).mul hh
  refine h.congr_deriv ?_
  have hs : ((sA t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sA_ne t)
  simp only [Fdotf, Thdot]
  push_cast
  field_simp
  ring

/-! ### The mixed derivatives -/

theorem hasDerivAt_Thdot_space (t s : ℝ) : HasDerivAt (Thdot t) (Thdots t s) s := by
  simpa [Thdot, Thdots] using (hasDerivAt_id s).mul_const (cA t * profD t)

theorem hasDerivAt_ww_space (t s : ℝ) : HasDerivAt (ww t) 0 s := hasDerivAt_const s (profD t)

theorem hasDerivAt_Fdot_space (t s : ℝ) : HasDerivAt (Fdotf t) (Fdotsf t s) s := by
  have hth := ((hasDerivAt_ofReal_Th t s).const_mul Complex.I).cexp
  have hb : HasDerivAt (fun y : ℝ => (((-1 / (sA t) ^ 2 : ℝ) : ℂ)
      + Complex.I * ((y / sA t : ℝ) : ℂ)))
      (Complex.I * ((1 / sA t : ℝ) : ℂ)) s := by
    have h0 : HasDerivAt (fun y : ℝ => ((y / sA t : ℝ) : ℂ))
        (((1 / sA t : ℝ) : ℂ)) s := by
      simpa using ((hasDerivAt_id s).div_const (sA t)).ofReal_comp
    simpa using (h0.const_mul Complex.I).const_add (((-1 / (sA t) ^ 2 : ℝ) : ℂ))
  have h := (((hth.const_mul (-Complex.I)).mul_const (((cA t * profD t : ℝ) : ℂ))).mul hb)
  refine h.congr_deriv ?_
  have hs : ((sA t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sA_ne t)
  simp only [Fdotsf, Th]
  push_cast
  field_simp
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-((s : ℂ) * (sA t : ℂ) * (cA t : ℂ) * (profD t : ℂ))) * hI

theorem hasDerivAt_sff_time (t x : ℝ) : HasDerivAt (fun r => sff r x) (sfft t x) t := by
  have h := (hasDerivAt_const t x).div (hasDerivAt_cA t) (cA_ne t)
  refine h.congr_deriv ?_
  simp only [sfft]
  field_simp
  ring

/-! ### The geometry of the slices -/

theorem sff_inv (t x : ℝ) : rearArclength (de t) (sff t x) = x := by
  simp only [rearArclength, de, sff]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  have hcos : Real.cos (prof t) = cA t := rfl
  rw [hcos]
  exact div_mul_cancel₀ x (cA_ne t)

theorem de_periodic (t : ℝ) : Function.Periodic (de t) (Pp t) := fun _ => rfl

theorem Ff_periodic (t s : ℝ) : Ff t (s + Pp t) = Ff t s := by
  have hs : sA t ≠ 0 := sA_ne t
  have hshift : Th t (s + Pp t) = Th t s + 2 * Real.pi := by
    simp only [Th, Pp]
    field_simp
  simp only [Ff, hshift]
  push_cast
  rw [mul_add, Complex.exp_add,
    show Complex.I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_two_pi_mul_I, mul_one]

theorem Th_periodic (t s : ℝ) : Th t (s + Pp t) = Th t s + 2 * Real.pi := by
  have hs : sA t ≠ 0 := sA_ne t
  simp only [Th, Pp]
  field_simp

/-! ### The rear period -/

theorem rearPeriod_eq (t : ℝ) :
    rearArclength (de t) (Pp t) = 2 * Real.pi * cA t / sA t := by
  simp only [rearArclength, de, Pp]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  have hcos : Real.cos (prof t) = cA t := rfl
  rw [hcos]
  field_simp

theorem rearPeriod_zero : rearArclength (de 0) (Pp 0) = 2 * Real.pi := by
  rw [rearPeriod_eq, cA_zero, sA_zero]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

theorem rearPeriod_one : rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 := by
  rw [rearPeriod_eq, cA_one, sA_one]
  ring

/-- **The length of the rear really moves.** -/
theorem rearPeriod_ne : rearArclength (de 0) (Pp 0) ≠ rearArclength (de 1) (Pp 1) := by
  rw [rearPeriod_zero, rearPeriod_one]
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    have : Real.sqrt 1 < Real.sqrt 3 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  have hpi := Real.pi_pos
  nlinarith

/-! ### Regularity -/

@[fun_prop]
theorem contDiff_uncurry_Th : ContDiff ℝ (⊤ : ℕ∞) (uncurry Th) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => p.2 * sA p.1
  fun_prop

@[fun_prop]
theorem contDiff_uncurry_de : ContDiff ℝ (⊤ : ℕ∞) (uncurry de) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => prof p.1
  fun_prop

@[fun_prop]
theorem contDiff_uncurry_Ff : ContDiff ℝ (⊤ : ℕ∞) (uncurry Ff) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ =>
    -Complex.I * ((1 / sA p.1 : ℝ) : ℂ) * Complex.exp (Complex.I * ((p.2 * sA p.1 : ℝ) : ℂ))
  fun_prop (disch := intros; simp [sA_ne])

theorem rearOwnAngle_eq (t x : ℝ) :
    rearOwnAngle Th de sff t x = x / cA t * sA t - prof t := rfl

@[fun_prop]
theorem contDiff_uncurry_ang : ContDiff ℝ (⊤ : ℕ∞) (uncurry (rearOwnAngle Th de sff)) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => p.2 / cA p.1 * sA p.1 - prof p.1
  fun_prop (disch := intros; simp [cA_ne])

@[fun_prop]
theorem contDiff_uncurry_Ydot : ContDiff ℝ (⊤ : ℕ∞) (uncurry Ydotf) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ =>
    trackVelocity Fdotf Thdot ww Th de p.1 (sff p.1 p.2) + (sfft p.1 p.2) •
      ((Real.cos (de p.1 (sff p.1 p.2)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Th p.1) (de p.1) (sff p.1 p.2) : ℂ)))
  simp only [trackVelocity, rearAngle, Th, de, sff, sfft, Fdotf, Thdot, ww]
  fun_prop (disch := intros; simp [sA_ne, cA_ne])

/-! ### The normal velocity of the front -/

theorem etaF_eq (t s : ℝ) : etaFf t s = frontNormalVelocityAt Fdotf Th de t s := by
  have hexp : Complex.exp (Complex.I * (Th t s : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (Th t s : ℂ))) = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq]
    simp [Complex.norm_exp]
  simp only [frontNormalVelocityAt, SelectedInverseJacobiODE.frontNormalVelocity, rearAngle,
    Fdotf, etaFf]
  have hpsi : Th t s - de t s + de t s = Th t s := by ring
  rw [hpsi]
  rw [map_mul, Complex.conj_I]
  have hkey : -Complex.I * Complex.exp (Complex.I * (Th t s : ℂ)) * ((cA t * profD t : ℝ) : ℂ)
      * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))
      * (-Complex.I * (starRingEnd ℂ) (Complex.exp (Complex.I * (Th t s : ℂ))))
      = -(((cA t * profD t : ℝ) : ℂ)
          * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (((cA t * profD t : ℝ) : ℂ)
      * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ))
      * (Complex.exp (Complex.I * (Th t s : ℂ))
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (Th t s : ℂ))))) * hI
      + (-(((cA t * profD t : ℝ) : ℂ)
        * (((-1 / (sA t) ^ 2 : ℝ) : ℂ) + Complex.I * ((s / sA t : ℝ) : ℂ)))) * hexp
  rw [hkey]
  simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

/-! ### Norms -/

theorem norm_expI (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

theorem norm_Ff (t s : ℝ) : ‖Ff t s‖ = 1 / sA t := by
  rw [Ff, norm_mul, norm_mul, norm_expI, norm_neg, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by exact one_div_pos.mpr (sA_pos t))]
  ring

theorem norm_rearOwn_le (t y : ℝ) : ‖rearOwn Ff Th de sff t y‖ ≤ 1 / sA t + 1 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_Ff, norm_expI]

/-! ### The family is frozen when the profile is -/

theorem Ydot_eq_zero {t : ℝ} (h : profD t = 0) (x : ℝ) : Ydotf t x = 0 := by
  simp [Ydotf, trackVelocity, Fdotf, Thdot, ww, sfft, h]

end MovingCircle
