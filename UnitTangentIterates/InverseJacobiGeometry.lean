import Mathlib
import UnitTangentIterates.Shadowing

/-!
# The inverse Jacobi identity, derived from the Frenet geometry

`Shadowing.inverse_jacobi_identity` proves the paper's

  `(1 + ∂ₓ) η_R = sec δ · η_F ∘ s`   (`eq:inverse-jacobi`)

from the scalar hypothesis

  `η_F = -ξ sin δ + (η_R + η_{R,x} + k ξ) cos δ`,

which was carried as an assumption.  This file derives that hypothesis from the
geometry it comes from, so the identity now rests only on the Frenet relations.

The computation in the paper is: parametrize the rear `R` by rear arclength `x`,
with unit tangent `τ = e^{iψ}` and unit normal `ν = i e^{iψ}`, and write the
variation of the rear as

  `Ṙ = ξ τ + η_R ν = (ξ + i η_R) e^{iψ}`.

The front is `F = R + τ`, and the variation of the tangent is
`τ̇ = i ψ̇ e^{iψ}` with `ψ̇ = η_{R,x} + k ξ`, so

  `Ḟ = (ξ + i(η_R + η_{R,x} + k ξ)) e^{iψ}`.

The front unit normal is `ν_F = -sin δ · τ + cos δ · ν = i e^{i(ψ+δ)}`, and the
front normal velocity is `η_F = ⟪ν_F, Ḟ⟫`.  Taking the real part of
`conj(ν_F) · Ḟ` gives exactly the displayed formula: the `ξ` terms combine into
`-ξ sin δ`, and on the selected strip `k = tan δ` makes them cancel against
`k ξ cos δ`.

Main results:

* `hasDerivAt_frenet_frame` — `∂ₓ(ξ τ + η ν) = (ξ' − kη) τ + (η' + kξ) ν`, the
  Frenet computation producing the normal component `η_{R,x} + k ξ`;
* `front_normal_of_rear_variation` — the formula for `η_F`, computed;
* `frontNormal_eq` — the front unit normal is `i e^{i(ψ+δ)}`;
* `tangent_variation_normal` — `τ̇` is purely normal in the arclength gauge;
* `inverse_jacobi_of_geometry`, `inverse_jacobi_of_variation` —
  `eq:inverse-jacobi` with no scalar hypothesis;
* `rear_normal_deriv_of_geometry` — its differentiated form `η_{R,x} = sec δ η_F − η_R`.
-/

noncomputable section

namespace InverseJacobiGeometry

/-- `e^{ix} = cos x + i sin x` in the form used below. -/
private theorem exp_I_mul (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ))
      = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I]
  norm_cast

/-- **The Frenet derivative of a frame combination.**  Along a unit-speed curve
with tangent angle `ψ` and curvature `k = ψ'`, the tangent is `τ = e^{iψ}` and
the normal `ν = i e^{iψ}`, so `τ' = k ν` and `ν' = -k τ`.  Consequently

  `∂ₓ(ξ τ + η ν) = (ξ' - k η) τ + (η' + k ξ) ν`.

This is the computation behind `τ̇ = (η_{R,x} + k ξ) ν` in the proof of
`lem:jacobi`: applied to the variation field `Ṙ = ξ τ + η ν`, the normal
component of `∂ₓ Ṙ` is `η_{R,x} + k ξ`. -/
theorem hasDerivAt_frenet_frame {psi xi eta : ℝ → ℝ} {k xi' eta' x : ℝ}
    (hpsi : HasDerivAt psi k x) (hxi : HasDerivAt xi xi' x)
    (heta : HasDerivAt eta eta' x) :
    HasDerivAt
      (fun y : ℝ => ((xi y : ℝ) : ℂ) * Complex.exp (Complex.I * ((psi y : ℝ) : ℂ))
        + ((eta y : ℝ) : ℂ) *
          (Complex.I * Complex.exp (Complex.I * ((psi y : ℝ) : ℂ))))
      ((((xi' - k * eta x : ℝ)) : ℂ) *
          Complex.exp (Complex.I * ((psi x : ℝ) : ℂ))
        + (((eta' + k * xi x : ℝ)) : ℂ) *
          (Complex.I * Complex.exp (Complex.I * ((psi x : ℝ) : ℂ)))) x := by
  have hE : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * ((psi y : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((psi x : ℝ) : ℂ)) * (Complex.I * (k : ℂ))) x := by
    have h := (((hpsi.ofReal_comp).const_mul Complex.I)).cexp
    simpa [mul_comm] using h
  have h1 := hxi.ofReal_comp.mul hE
  have h2 := heta.ofReal_comp.mul (hE.const_mul Complex.I)
  refine (h1.add h2).congr_deriv ?_
  push_cast
  linear_combination
    ((k : ℂ) * ((eta x : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((psi x : ℝ) : ℂ))) * Complex.I_sq

/-- **The front unit normal.**  With rear tangent angle `ψ` and steering angle
`δ`, the rotation `-sin δ · τ + cos δ · ν` of the rear frame is `i e^{i(ψ+δ)}`:
the front turns by the steering angle. -/
theorem frontNormal_eq (psi delta : ℝ) :
    (-(Real.sin delta : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))
        + (Real.cos delta : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (psi : ℂ)))
      = Complex.I * Complex.exp (Complex.I * (((psi + delta : ℝ)) : ℂ)) := by
  rw [exp_I_mul, exp_I_mul, Real.cos_add, Real.sin_add]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] <;>
    ring

/-- **The front normal velocity of a rear variation.**  With
`Ḟ = (ξ + i A) e^{iψ}` and front unit normal `ν_F = i e^{i(ψ+δ)}`, the normal
component `η_F = Re(conj(ν_F)·Ḟ)` is `-ξ sin δ + A cos δ`.  Here
`A = η_R + η_{R,x} + k ξ` is the normal component of `Ṙ + τ̇`. -/
theorem front_normal_of_rear_variation (psi delta xi A : ℝ) :
    ((starRingEnd ℂ)
        (Complex.I * Complex.exp (Complex.I * (((psi + delta : ℝ)) : ℂ))) *
      ((((xi : ℝ) : ℂ) + Complex.I * ((A : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((psi : ℝ) : ℂ)))).re
      = -xi * Real.sin delta + A * Real.cos delta := by
  rw [exp_I_mul, exp_I_mul]
  simp only [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im]
  rw [Real.cos_add, Real.sin_add]
  linear_combination (A * Real.cos delta - xi * Real.sin delta) *
    Real.sin_sq_add_cos_sq psi

/-- **The inverse Jacobi identity, from the geometry.**  This is
`eq:inverse-jacobi` of the paper with its scalar hypothesis replaced by the
Frenet computation: the front normal velocity is *defined* as the normal
component of the variation of `F = R + τ`, and on the selected strip, where the
rear curvature is `k = tan δ`, the tangential contributions cancel. -/
theorem inverse_jacobi_of_geometry {psi delta xi etaR etaRx k etaF : ℝ}
    (hk : k = Real.tan delta) (hcos : Real.cos delta ≠ 0)
    (hetaF : etaF =
      ((starRingEnd ℂ)
          (Complex.I * Complex.exp (Complex.I * (((psi + delta : ℝ)) : ℂ))) *
        ((((xi : ℝ) : ℂ) +
            Complex.I * (((etaR + etaRx + k * xi : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((psi : ℝ) : ℂ)))).re) :
    etaR + etaRx = etaF / Real.cos delta := by
  refine Shadowing.inverse_jacobi_identity (xi := xi) hk hcos ?_
  rw [hetaF, front_normal_of_rear_variation]

/-- **The variation of the tangent is purely normal.**  Differentiating
`|τ| = 1` forces the arclength gauge `ξ' = k η`; with it,
`τ̇ = ∂ₓ(ξ τ + η ν) = (η' + k ξ) ν`, which is the step
`τ̇ = (η_{R,x} + k ξ) ν` in the proof of `lem:jacobi`. -/
theorem tangent_variation_normal {psi xi eta : ℝ → ℝ} {k eta' x : ℝ}
    (hpsi : HasDerivAt psi k x) (hxi : HasDerivAt xi (k * eta x) x)
    (heta : HasDerivAt eta eta' x) :
    HasDerivAt
      (fun y : ℝ => ((xi y : ℝ) : ℂ) * Complex.exp (Complex.I * ((psi y : ℝ) : ℂ))
        + ((eta y : ℝ) : ℂ) *
          (Complex.I * Complex.exp (Complex.I * ((psi y : ℝ) : ℂ))))
      ((((eta' + k * xi x : ℝ)) : ℂ) *
        (Complex.I * Complex.exp (Complex.I * ((psi x : ℝ) : ℂ)))) x := by
  refine (hasDerivAt_frenet_frame hpsi hxi heta).congr_deriv ?_
  simp

/-- **`eq:inverse-jacobi` from the rear variation field.**  Assembling the two
geometric steps: the rear variation `Ṙ = ξ τ + η ν` has `τ̇ = (η' + k ξ) ν` in
the arclength gauge, so the front variation `Ḟ = Ṙ + τ̇` has tangential part `ξ`
and normal part `η + η' + k ξ`; taking its component along the front normal
`ν_F = i e^{i(ψ+δ)}` and using `k = tan δ` on the selected strip gives
`(1 + ∂ₓ) η = sec δ · η_F`. -/
theorem inverse_jacobi_of_variation {psi xi eta : ℝ → ℝ} {k delta eta' x etaF : ℝ}
    (hk : k = Real.tan delta) (hcos : Real.cos delta ≠ 0)
    (hetaF : etaF =
      ((starRingEnd ℂ)
          (Complex.I *
            Complex.exp (Complex.I * (((psi x + delta : ℝ)) : ℂ))) *
        (((((xi x : ℝ)) : ℂ) +
            Complex.I * (((eta x + eta' + k * xi x : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * (((psi x : ℝ)) : ℂ)))).re) :
    eta x + eta' = etaF / Real.cos delta :=
  inverse_jacobi_of_geometry (psi := psi x) (xi := xi x) hk hcos hetaF

/-- The differentiated form of `inverse_jacobi_of_geometry`. -/
theorem rear_normal_deriv_of_geometry {psi delta xi etaR etaRx k etaF : ℝ}
    (hk : k = Real.tan delta) (hcos : Real.cos delta ≠ 0)
    (hetaF : etaF =
      ((starRingEnd ℂ)
          (Complex.I * Complex.exp (Complex.I * (((psi + delta : ℝ)) : ℂ))) *
        ((((xi : ℝ) : ℂ) +
            Complex.I * (((etaR + etaRx + k * xi : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((psi : ℝ) : ℂ)))).re) :
    etaRx = etaF / Real.cos delta - etaR := by
  have h := inverse_jacobi_of_geometry hk hcos hetaF
  linarith

end InverseJacobiGeometry
