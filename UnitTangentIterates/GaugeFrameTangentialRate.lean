import Mathlib
import UnitTangentIterates.GaugeFrameTimeBounds

/-!
# The tangential rate of a family carried in its own arclength

`GaugeFrameTimeBounds.angleRate_eq` derives `∂_tα = ∂_sη + kξ` from the equality
of the mixed partial derivatives of the position, *assuming* the identity
`∂_sξ = kη` that preserves the arclength parametrization.  That identity is not
an extra assumption: it is the other half of the same equality.

Indeed, writing the velocity of the family in its moving frame,
`∂_tY = ξ e^{iα} + η · i e^{iα}`, its arclength derivative is

```
  ∂_s(∂_tY) = (∂_sξ − kη) · e^{iα} + (∂_sη + kξ) · i e^{iα} ,
```

while the time derivative of the unit tangent `∂_sY = e^{iα}` is
`∂_t(∂_sY) = ∂_tα · i e^{iα}`, which has no component along `e^{iα}`.  Comparing
the two components of one complex identity therefore gives *both*

```
  ∂_sξ = kη        and        ∂_tα = ∂_sη + kξ .
```

Main result: `tangentialRate_eq`.
-/

noncomputable section

namespace GaugeFrameTangentialRate

/-- **Both normal-flow relations, from the equality of the mixed partial
derivatives alone.**  For a family carried in its own arclength, moving with
tangential rate `ξ` and normal rate `η`, the component of the identity
`∂_s∂_tY = ∂_t∂_sY` along the unit tangent says that the arclength
parametrization is preserved, `∂_sξ = kη`, and the component along the normal
says that the tangent angle turns at the rate `∂_sη + kξ`. -/
theorem tangentialRate_eq {alpha k xi xiS eta etaS alphaT : ℝ → ℝ → ℝ} {W : ℂ} (t s : ℝ)
    (halphaS : ∀ x, HasDerivAt (alpha t) (k t x) x)
    (hetaS : ∀ x, HasDerivAt (eta t) (etaS t x) x)
    (hxiS : ∀ x, HasDerivAt (xi t) (xiS t x) x)
    (halphaT : HasDerivAt (fun r => alpha r s) (alphaT t s) t)
    (htangent : HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t)
    (hvel : HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (eta t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s) :
    xiS t s = k t s * eta t s ∧ alphaT t s = etaS t s + k t s * xi t s := by
  -- the time derivative of the unit tangent
  have hT : HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ)))
      (Complex.I * ((alphaT t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))) t := by
    have h1 : HasDerivAt (fun r => Complex.I * ((alpha r s : ℝ) : ℂ))
        (Complex.I * ((alphaT t s : ℝ) : ℂ)) t := halphaT.ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  -- the arclength derivative of the unit tangent
  have hexp : ∀ x, HasDerivAt (fun y => Complex.exp (Complex.I * (alpha t y : ℂ)))
      (Complex.I * ((k t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y => Complex.I * ((alpha t y : ℝ) : ℂ))
        (Complex.I * ((k t x : ℝ) : ℂ)) x := (halphaS x).ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  -- the arclength derivative of the velocity, in the moving frame
  have hV : HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
      + (eta t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
      (((xiS t s - k t s * eta t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + ((etaS t s + k t s * xi t s : ℝ) : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) s := by
    have h1 := ((hxiS s).ofReal_comp.mul (hexp s))
    have h2 := ((hetaS s).ofReal_comp.mul ((hexp s).const_mul Complex.I))
    have h := h1.add h2
    refine h.congr_deriv ?_
    push_cast
    linear_combination ((k t s : ℂ) * (eta t s : ℂ)
      * Complex.exp (Complex.I * (alpha t s : ℂ))) * Complex.I_sq
  -- the two agree, and the exponential does not vanish
  have heq : Complex.I * ((alphaT t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
      = ((xiS t s - k t s * eta t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + ((etaS t s + k t s * xi t s : ℝ) : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ))) := by
    rw [hT.unique htangent, hvel.unique hV]
  have hne : Complex.exp (Complex.I * (alpha t s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have heq' : Complex.I * ((alphaT t s : ℝ) : ℂ)
      = ((xiS t s - k t s * eta t s : ℝ) : ℂ)
        + ((etaS t s + k t s * xi t s : ℝ) : ℂ) * Complex.I := by
    refine mul_right_cancel₀ hne ?_
    rw [heq]
    ring
  -- the component along the tangent and the component along the normal
  have hre := congrArg Complex.re heq'
  have him := congrArg Complex.im heq'
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  constructor
  · linarith
  · linarith

end GaugeFrameTangentialRate
